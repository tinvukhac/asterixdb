/*
 * Licensed to the Apache Software Foundation (ASF) under one
 * or more contributor license agreements.  See the NOTICE file
 * distributed with this work for additional information
 * regarding copyright ownership.  The ASF licenses this file
 * to you under the Apache License, Version 2.0 (the
 * "License"); you may not use this file except in compliance
 * with the License.  You may obtain a copy of the License at
 *
 *   http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing,
 * software distributed under the License is distributed on an
 * "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY
 * KIND, either express or implied.  See the License for the
 * specific language governing permissions and limitations
 * under the License.
 */
package org.apache.asterix.external.parser;

import static org.apache.asterix.external.util.ExternalDataConstants.MISSING_FIELDS;

import java.io.DataOutput;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.util.function.Supplier;

import org.apache.asterix.builders.IARecordBuilder;
import org.apache.asterix.builders.RecordBuilder;
import org.apache.asterix.common.exceptions.ErrorCode;
import org.apache.asterix.common.exceptions.RuntimeDataException;
import org.apache.asterix.external.api.IDataParser;
import org.apache.asterix.external.api.IRawRecord;
import org.apache.asterix.external.api.IRecordDataParser;
import org.apache.asterix.external.api.IStreamDataParser;
import org.apache.asterix.external.util.ExternalDataConstants;
import org.apache.asterix.external.util.ParseUtil;
import org.apache.asterix.om.base.AMutableString;
import org.apache.asterix.om.types.ARecordType;
import org.apache.asterix.om.types.ATypeTag;
import org.apache.asterix.om.utils.NonTaggedFormatUtil;
import org.apache.hyracks.api.context.IHyracksTaskContext;
import org.apache.hyracks.api.exceptions.HyracksDataException;
import org.apache.hyracks.api.exceptions.IWarningCollector;
import org.apache.hyracks.data.std.util.ArrayBackedValueStorage;
import org.apache.hyracks.dataflow.common.data.parsers.IValueParser;
import org.apache.hyracks.dataflow.common.data.parsers.IValueParserFactory;
import org.apache.hyracks.dataflow.std.file.FieldCursorForDelimitedDataParser;

public class DelimitedDataParser extends AbstractDataParser implements IStreamDataParser, IRecordDataParser<char[]> {

    private final IWarningCollector warnings;
    private final char fieldDelimiter;
    private final char quote;
    private final boolean hasHeader;
    private final ARecordType recordType;
    private final IARecordBuilder recBuilder;
    private final ArrayBackedValueStorage fieldValueBuffer;
    private final DataOutput fieldValueBufferOutput;
    private final IValueParser[] valueParsers;
    private FieldCursorForDelimitedDataParser cursor;
    private Supplier<String> dataSourceName;
    private final byte[] fieldTypeTags;
    private final int[] fldIds;
    private final ArrayBackedValueStorage[] nameBuffers;

    public DelimitedDataParser(IHyracksTaskContext ctx, IValueParserFactory[] valueParserFactories, char fieldDelimiter,
            char quote, boolean hasHeader, ARecordType recordType, boolean isStreamParser) throws HyracksDataException {
        this.dataSourceName = ExternalDataConstants.EMPTY_STRING;
        this.warnings = ctx.getWarningCollector();
        this.fieldDelimiter = fieldDelimiter;
        this.quote = quote;
        this.hasHeader = hasHeader;
        this.recordType = recordType;
        valueParsers = new IValueParser[valueParserFactories.length];
        for (int i = 0; i < valueParserFactories.length; ++i) {
            valueParsers[i] = valueParserFactories[i].createValueParser();
        }

        fieldValueBuffer = new ArrayBackedValueStorage();
        fieldValueBufferOutput = fieldValueBuffer.getDataOutput();
        recBuilder = new RecordBuilder();
        recBuilder.reset(recordType);
        recBuilder.init();

        int n = recordType.getFieldNames().length;
        fieldTypeTags = new byte[n];
        for (int i = 0; i < n; i++) {
            ATypeTag tag = recordType.getFieldTypes()[i].getTypeTag();
            fieldTypeTags[i] = tag.serialize();
        }

        fldIds = new int[n];
        nameBuffers = new ArrayBackedValueStorage[n];
        AMutableString str = new AMutableString(null);
        for (int i = 0; i < n; i++) {
            String name = recordType.getFieldNames()[i];
            fldIds[i] = recBuilder.getFieldId(name);
            if (fldIds[i] < 0) {
                if (!recordType.isOpen()) {
                    throw new RuntimeDataException(ErrorCode.PARSER_DELIMITED_ILLEGAL_FIELD, name, recordType);
                } else {
                    nameBuffers[i] = new ArrayBackedValueStorage();
                    str.setValue(name);
                    IDataParser.toBytes(str, nameBuffers[i], stringSerde);
                }
            }
        }
        if (!isStreamParser) {
            cursor = new FieldCursorForDelimitedDataParser(null, this.fieldDelimiter, quote, warnings, dataSourceName);
        }
    }

    @Override
    public boolean parse(DataOutput out) throws HyracksDataException {
        try {
            while (cursor.nextRecord()) {
                if (parseRecord()) {
                    recBuilder.write(out, true);
                    return true;
                } else {
                    // keeping the behaviour of throwing exception for stream parsers
                    throw new RuntimeDataException(ErrorCode.FAILED_TO_PARSE_RECORD);
                }
            }
            return false;
        } catch (IOException e) {
            throw HyracksDataException.create(e);
        }
    }

    private boolean parseRecord() throws HyracksDataException {
        recBuilder.reset(recordType);
        recBuilder.init();

        for (int i = 0; i < valueParsers.length; ++i) {
            try {
                FieldCursorForDelimitedDataParser.Result result = cursor.nextField();
                switch (result) {
                    case OK:
                        break;
                    case END:
                        if (warnings.shouldWarn()) {
                            ParseUtil.warn(warnings, dataSourceName.get(), cursor.getRecordCount(),
                                    cursor.getFieldCount(), MISSING_FIELDS);
                        }
                        return false;
                    case ERROR:
                        return false;
                    default:
                        throw new IllegalStateException();
                }
                fieldValueBuffer.reset();

                if (cursor.isFieldEmpty() && recordType.getFieldTypes()[i].getTypeTag() != ATypeTag.STRING
                        && recordType.getFieldTypes()[i].getTypeTag() != ATypeTag.NULL) {
                    // if the field is empty and the type is optional, insert
                    // NULL. Note that string type can also process empty field as an
                    // empty string
                    if (!NonTaggedFormatUtil.isOptional(recordType.getFieldTypes()[i])) {
                        throw new RuntimeDataException(ErrorCode.PARSER_DELIMITED_NONOPTIONAL_NULL,
                                cursor.getRecordCount(), cursor.getFieldCount());
                    }
                    fieldValueBufferOutput.writeByte(ATypeTag.SERIALIZED_NULL_TYPE_TAG);
                } else {
                    fieldValueBufferOutput.writeByte(fieldTypeTags[i]);
                    // Eliminate double quotes in the field that we are going to parse
                    if (cursor.fieldHasDoubleQuote()) {
                        cursor.eliminateDoubleQuote();
                    }
                    valueParsers[i].parse(cursor.getBuffer(), cursor.getFieldStart(), cursor.getFieldLength(),
                            fieldValueBufferOutput);
                }
                if (fldIds[i] < 0) {
                    recBuilder.addField(nameBuffers[i], fieldValueBuffer);
                } else {
                    recBuilder.addField(fldIds[i], fieldValueBuffer);
                }
            } catch (IOException e) {
                throw HyracksDataException.create(e);
            }
        }
        return true;
    }

    @Override
    public boolean parse(IRawRecord<? extends char[]> record, DataOutput out) throws HyracksDataException {
        cursor.nextRecord(record.get(), record.size());
        if (parseRecord()) {
            recBuilder.write(out, true);
            return true;
        }
        return false;
    }

    @Override
    public void setInputStream(InputStream in) throws IOException {
        // TODO(ali): revisit this in regards to stream
        cursor = new FieldCursorForDelimitedDataParser(new InputStreamReader(in), fieldDelimiter, quote, warnings,
                dataSourceName);
        if (hasHeader) {
            cursor.nextRecord();
            FieldCursorForDelimitedDataParser.Result result;
            do {
                result = cursor.nextField();
            } while (result == FieldCursorForDelimitedDataParser.Result.OK);
            if (result == FieldCursorForDelimitedDataParser.Result.ERROR) {
                throw new RuntimeDataException(ErrorCode.FAILED_TO_PARSE_RECORD);
            }
        }
    }

    @Override
    public boolean reset(InputStream in) throws IOException {
        // TODO(ali): revisit this in regards to stream
        cursor = new FieldCursorForDelimitedDataParser(new InputStreamReader(in), fieldDelimiter, quote, warnings,
                dataSourceName);
        return true;
    }

    @Override
    public void setDataSourceName(Supplier<String> dataSourceName) {
        this.dataSourceName = dataSourceName == null ? ExternalDataConstants.EMPTY_STRING : dataSourceName;
    }
}
