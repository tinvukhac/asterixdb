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
package org.apache.asterix.runtime.aggregates.std;

import java.io.ByteArrayInputStream;
import java.io.DataInput;
import java.io.DataInputStream;
import java.io.IOException;

import org.apache.asterix.dataflow.data.nontagged.serde.ARectangleSerializerDeserializer;
import org.apache.asterix.formats.nontagged.SerializerDeserializerProvider;
import org.apache.asterix.om.base.APoint;
import org.apache.asterix.om.base.ARectangle;
import org.apache.asterix.om.functions.BuiltinFunctions;
import org.apache.asterix.om.types.ATypeTag;
import org.apache.asterix.om.types.BuiltinType;
import org.apache.asterix.om.types.EnumDeserializer;
import org.apache.asterix.runtime.exceptions.UnsupportedItemTypeException;
import org.apache.hyracks.algebricks.runtime.base.IEvaluatorContext;
import org.apache.hyracks.algebricks.runtime.base.IScalarEvaluator;
import org.apache.hyracks.algebricks.runtime.base.IScalarEvaluatorFactory;
import org.apache.hyracks.api.dataflow.value.ISerializerDeserializer;
import org.apache.hyracks.api.exceptions.HyracksDataException;
import org.apache.hyracks.api.exceptions.SourceLocation;
import org.apache.hyracks.data.std.api.IPointable;
import org.apache.hyracks.data.std.primitive.VoidPointable;
import org.apache.hyracks.data.std.util.ArrayBackedValueStorage;
import org.apache.hyracks.dataflow.common.data.accessors.IFrameTupleReference;

public abstract class AbstractUnionMbrAggregateFunction extends AbstractAggregateFunction {

    private ArrayBackedValueStorage resultStorage = new ArrayBackedValueStorage();
    private IPointable inputVal = new VoidPointable();
    private final IScalarEvaluator eval;
    protected final IEvaluatorContext context;
    protected double currentMinX;
    protected double currentMinY;
    protected double currentMaxX;
    protected double currentMaxY;

    private ISerializerDeserializer<ARectangle> rectangleSerde =
            SerializerDeserializerProvider.INSTANCE.getSerializerDeserializer(BuiltinType.ARECTANGLE);

    public AbstractUnionMbrAggregateFunction(IScalarEvaluatorFactory[] args, IEvaluatorContext context,
            SourceLocation sourceLoc) throws HyracksDataException {
        super(sourceLoc);
        this.eval = args[0].createScalarEvaluator(context);
        this.context = context;
    }

    @Override
    public void init() throws HyracksDataException {
        // Initialize the resulting mbr coordinates
        currentMinX = Double.POSITIVE_INFINITY;
        currentMinY = Double.POSITIVE_INFINITY;
        currentMaxX = Double.NEGATIVE_INFINITY;
        currentMaxY = Double.NEGATIVE_INFINITY;
    }

    @Override
    public void step(IFrameTupleReference tuple) throws HyracksDataException {
        eval.evaluate(tuple, inputVal);
        byte[] data = inputVal.getByteArray();
        int offset = inputVal.getStartOffset();
        int len = inputVal.getLength();
        ATypeTag typeTag =
                EnumDeserializer.ATYPETAGDESERIALIZER.deserialize(inputVal.getByteArray()[inputVal.getStartOffset()]);
        // Ignore SYSTEM_NULL.
        if (typeTag == ATypeTag.NULL || typeTag == ATypeTag.MISSING) {
            processNull();
        } else if (typeTag == ATypeTag.RECTANGLE) {
            DataInput dataIn = new DataInputStream(new ByteArrayInputStream(data, offset + 1, len - 1));
            ARectangle rect = ARectangleSerializerDeserializer.INSTANCE.deserialize(dataIn);
            currentMinX = Math.min(currentMinX, rect.getP1().getX());
            currentMinY = Math.min(currentMinY, rect.getP1().getY());
            currentMaxX = Math.max(currentMaxX, rect.getP2().getX());
            currentMaxY = Math.max(currentMaxY, rect.getP2().getY());
        }
    }

    @Override
    public void finish(IPointable result) throws HyracksDataException {
        resultStorage.reset();
        try {
            ARectangle unionMbr =
                    new ARectangle(new APoint(currentMinX, currentMinY), new APoint(currentMaxX, currentMaxY));
            rectangleSerde.serialize(unionMbr, resultStorage.getDataOutput());
        } catch (IOException e) {
            throw HyracksDataException.create(e);
        }
        result.set(resultStorage);
    }

    @Override
    public void finishPartial(IPointable result) throws HyracksDataException {
        if (isValidCoordinates(currentMinX, currentMinY, currentMaxX, currentMaxY)) {
            finish(result);
        }
    }

    protected void processNull() throws UnsupportedItemTypeException {
        throw new UnsupportedItemTypeException(sourceLoc, BuiltinFunctions.UNION_MBR,
                ATypeTag.SERIALIZED_SYSTEM_NULL_TYPE_TAG);
    }

    private boolean isValidCoordinates(double minX, double minY, double maxX, double maxY) {
        return (minX != Double.POSITIVE_INFINITY) && (minY != Double.POSITIVE_INFINITY)
                && (maxX != Double.NEGATIVE_INFINITY) && (maxY != Double.NEGATIVE_INFINITY);
    }
}
