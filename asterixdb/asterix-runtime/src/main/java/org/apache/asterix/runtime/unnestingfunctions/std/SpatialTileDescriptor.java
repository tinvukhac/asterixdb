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
package org.apache.asterix.runtime.unnestingfunctions.std;

import java.io.ByteArrayInputStream;
import java.io.DataInputStream;
import java.io.DataOutput;
import java.util.ArrayList;
import java.util.List;

import org.apache.asterix.dataflow.data.nontagged.Coordinate;
import org.apache.asterix.dataflow.data.nontagged.serde.ADoubleSerializerDeserializer;
import org.apache.asterix.dataflow.data.nontagged.serde.AInt64SerializerDeserializer;
import org.apache.asterix.dataflow.data.nontagged.serde.ARectangleSerializerDeserializer;
import org.apache.asterix.dataflow.data.nontagged.serde.AStringSerializerDeserializer;
import org.apache.asterix.formats.nontagged.SerializerDeserializerProvider;
import org.apache.asterix.om.base.AMutableInt32;
import org.apache.asterix.om.functions.BuiltinFunctions;
import org.apache.asterix.om.functions.IFunctionDescriptor;
import org.apache.asterix.om.functions.IFunctionDescriptorFactory;
import org.apache.asterix.om.types.ATypeTag;
import org.apache.asterix.om.types.BuiltinType;
import org.apache.asterix.om.types.EnumDeserializer;
import org.apache.asterix.runtime.exceptions.TypeMismatchException;
import org.apache.asterix.runtime.unnestingfunctions.base.AbstractUnnestingFunctionDynamicDescriptor;
import org.apache.hyracks.algebricks.core.algebra.functions.FunctionIdentifier;
import org.apache.hyracks.algebricks.runtime.base.IEvaluatorContext;
import org.apache.hyracks.algebricks.runtime.base.IScalarEvaluator;
import org.apache.hyracks.algebricks.runtime.base.IScalarEvaluatorFactory;
import org.apache.hyracks.algebricks.runtime.base.IUnnestingEvaluator;
import org.apache.hyracks.algebricks.runtime.base.IUnnestingEvaluatorFactory;
import org.apache.hyracks.api.context.IHyracksTaskContext;
import org.apache.hyracks.api.dataflow.value.ISerializerDeserializer;
import org.apache.hyracks.api.exceptions.HyracksDataException;
import org.apache.hyracks.data.std.api.IPointable;
import org.apache.hyracks.data.std.primitive.VoidPointable;
import org.apache.hyracks.data.std.util.ArrayBackedValueStorage;
import org.apache.hyracks.dataflow.common.data.accessors.IFrameTupleReference;
import org.apache.hyracks.dataflow.common.utils.TaskUtil;

public class SpatialTileDescriptor extends AbstractUnnestingFunctionDynamicDescriptor {
    private static final long serialVersionUID = 1L;

    public static final IFunctionDescriptorFactory FACTORY = new IFunctionDescriptorFactory() {
        @Override
        public IFunctionDescriptor createFunctionDescriptor() {
            return new SpatialTileDescriptor();
        }
    };

    @Override
    public FunctionIdentifier getIdentifier() {
        return BuiltinFunctions.SPATIAL_TILE;
    }

    @Override
    public IUnnestingEvaluatorFactory createUnnestingEvaluatorFactory(final IScalarEvaluatorFactory[] args) {
        return new IUnnestingEvaluatorFactory() {

            private static final long serialVersionUID = 1L;

            @Override
            public IUnnestingEvaluator createUnnestingEvaluator(final IEvaluatorContext ctx)
                    throws HyracksDataException {
                final IHyracksTaskContext hyracksTaskContext = ctx.getTaskContext();

                return new IUnnestingEvaluator() {
                    private final ArrayBackedValueStorage resultStorage = new ArrayBackedValueStorage();
                    private List<Integer> tileValues = new ArrayList<>();
                    private final DataOutput out = resultStorage.getDataOutput();
                    private final IPointable inputArg0 = new VoidPointable();
                    private final IPointable inputArg1 = new VoidPointable();
                    private final IPointable inputArg2 = new VoidPointable();
                    private final IPointable inputArg3 = new VoidPointable();
                    private final IPointable inputArg4 = new VoidPointable();
                    private final IScalarEvaluator eval0 = args[0].createScalarEvaluator(ctx);
                    private final IScalarEvaluator eval1 = args[1].createScalarEvaluator(ctx);
                    private final IScalarEvaluator eval2 = args[2].createScalarEvaluator(ctx);
                    private final IScalarEvaluator eval3 = args[3].createScalarEvaluator(ctx);
                    private final IScalarEvaluator eval4 = args[4].createScalarEvaluator(ctx);

                    private AMutableInt32 aInt32 = new AMutableInt32(0);
                    int pos;

                    @SuppressWarnings("unchecked")
                    private ISerializerDeserializer intSerde =
                            SerializerDeserializerProvider.INSTANCE.getSerializerDeserializer(BuiltinType.AINT32);

                    @Override
                    public void init(IFrameTupleReference tuple) throws HyracksDataException {
                        eval0.evaluate(tuple, inputArg0);
                        eval1.evaluate(tuple, inputArg1);
                        eval2.evaluate(tuple, inputArg2);
                        eval3.evaluate(tuple, inputArg3);
                        eval4.evaluate(tuple, inputArg4);

                        byte[] bytes0 = inputArg0.getByteArray();
                        byte[] bytes1 = inputArg1.getByteArray();
                        byte[] bytes2 = inputArg2.getByteArray();
                        byte[] bytes3 = inputArg3.getByteArray();
                        byte[] bytes4 = inputArg4.getByteArray();

                        int offset0 = inputArg0.getStartOffset();
                        int offset1 = inputArg1.getStartOffset();
                        int offset2 = inputArg2.getStartOffset();
                        int offset3 = inputArg3.getStartOffset();
                        int offset4 = inputArg4.getStartOffset();

                        ATypeTag tag0 = EnumDeserializer.ATYPETAGDESERIALIZER.deserialize(bytes0[offset0]);
                        ATypeTag tag1 = EnumDeserializer.ATYPETAGDESERIALIZER.deserialize(bytes1[offset1]);
                        ATypeTag tag2 = EnumDeserializer.ATYPETAGDESERIALIZER.deserialize(bytes2[offset2]);
                        ATypeTag tag3 = EnumDeserializer.ATYPETAGDESERIALIZER.deserialize(bytes3[offset3]);
                        ATypeTag tag4 = EnumDeserializer.ATYPETAGDESERIALIZER.deserialize(bytes4[offset4]);

                        if ((tag0 == ATypeTag.RECTANGLE) && (tag1 == ATypeTag.RECTANGLE) && (tag2 == ATypeTag.BIGINT)
                                && (tag3 == ATypeTag.BIGINT) && (tag4 == ATypeTag.STRING)) {
                            // Get dynamic MBR
                            ByteArrayInputStream keyInputStream =
                                    new ByteArrayInputStream(bytes4, offset4 + 1, inputArg4.getLength() - 1);
                            DataInputStream keyDataInputStream = new DataInputStream(keyInputStream);
                            String key = AStringSerializerDeserializer.INSTANCE.deserialize(keyDataInputStream)
                                    .getStringValue();
                            double minX, minY, maxX, maxY;

                            // key == empty mean we should use static MBR
                            if (key.equals("")) {
                                minX = ADoubleSerializerDeserializer.getDouble(bytes1, offset1 + 1
                                    + ARectangleSerializerDeserializer.getBottomLeftCoordinateOffset(Coordinate.X));
                                minY = ADoubleSerializerDeserializer.getDouble(bytes1, offset1 + 1
                                    + ARectangleSerializerDeserializer.getBottomLeftCoordinateOffset(Coordinate.Y));

                                maxX = ADoubleSerializerDeserializer.getDouble(bytes1, offset1 + 1
                                    + ARectangleSerializerDeserializer.getUpperRightCoordinateOffset(Coordinate.X));
                                maxY = ADoubleSerializerDeserializer.getDouble(bytes1, offset1 + 1
                                    + ARectangleSerializerDeserializer.getUpperRightCoordinateOffset(Coordinate.Y));
                            } else {
                                if (TaskUtil.get(key, hyracksTaskContext) != null) {
                                    Double[] mbrCoordinates = TaskUtil.get(key, hyracksTaskContext);
                                    minX = mbrCoordinates[0];
                                    minY = mbrCoordinates[1];
                                    maxX = mbrCoordinates[2];
                                    maxY = mbrCoordinates[3];
                                } else {
                                    throw HyracksDataException.create(
                                        new Throwable(String.format("%s: No MBR found", this.getClass().toString())));
                                }
                            }

                            double x1 = ADoubleSerializerDeserializer.getDouble(bytes0, offset0 + 1
                                + ARectangleSerializerDeserializer.getBottomLeftCoordinateOffset(Coordinate.X));
                            double y1 = ADoubleSerializerDeserializer.getDouble(bytes0, offset0 + 1
                                + ARectangleSerializerDeserializer.getBottomLeftCoordinateOffset(Coordinate.Y));

                            double x2 = ADoubleSerializerDeserializer.getDouble(bytes0, offset0 + 1
                                + ARectangleSerializerDeserializer.getUpperRightCoordinateOffset(Coordinate.X));
                            double y2 = ADoubleSerializerDeserializer.getDouble(bytes0, offset0 + 1
                                + ARectangleSerializerDeserializer.getUpperRightCoordinateOffset(Coordinate.Y));

                            int rows = (int) AInt64SerializerDeserializer.getLong(bytes2, offset2 + 1);
                            int columns = (int) AInt64SerializerDeserializer.getLong(bytes3, offset3 + 1);

                            int row1 = (int) Math.ceil((y1 - minY) * rows / (maxY - minY));
                            int col1 = (int) Math.ceil((x1 - minX) * columns / (maxX - minX));
                            int row2 = (int) Math.ceil((y2 - minY) * rows / (maxY - minY));
                            int col2 = (int) Math.ceil((x2 - minX) * columns / (maxX - minX));

                            row1 = Math.min(Math.max(1, row1), rows * columns);
                            col1 = Math.min(Math.max(1, col1), rows * columns);
                            row2 = Math.min(Math.max(1, row2), rows * columns);
                            col2 = Math.min(Math.max(1, col2), rows * columns);

                            int minRow = Math.min(row1, row2);
                            int maxRow = Math.max(row1, row2);
                            int minCol = Math.min(col1, col2);
                            int maxCol = Math.max(col1, col2);

                            tileValues.clear();
                            for (int i = minRow; i <= maxRow; i++) {
                                for (int j = minCol; j <= maxCol; j++) {
                                    int tileId = (i - 1) * columns + j;
                                    tileValues.add(tileId);
                                }
                            }
                            pos = 0;
                        } else {
                            if (tag0 != ATypeTag.RECTANGLE) {
                                throw new TypeMismatchException(sourceLoc, getIdentifier(), 0, bytes0[offset0],
                                        ATypeTag.SERIALIZED_RECTANGLE_TYPE_TAG);
                            }
                            if (tag1 != ATypeTag.RECTANGLE) {
                                throw new TypeMismatchException(sourceLoc, getIdentifier(), 0, bytes1[offset1],
                                        ATypeTag.SERIALIZED_RECTANGLE_TYPE_TAG);
                            }
                            if (tag2 != ATypeTag.BIGINT) {
                                throw new TypeMismatchException(sourceLoc, getIdentifier(), 0, bytes2[offset2],
                                        ATypeTag.SERIALIZED_INT64_TYPE_TAG);
                            }
                            if (tag3 != ATypeTag.BIGINT) {
                                throw new TypeMismatchException(sourceLoc, getIdentifier(), 0, bytes3[offset3],
                                        ATypeTag.SERIALIZED_INT64_TYPE_TAG);
                            }
                            if (tag4 != ATypeTag.STRING) {
                                throw new TypeMismatchException(sourceLoc, getIdentifier(), 0, bytes4[offset4],
                                        ATypeTag.SERIALIZED_STRING_TYPE_TAG);
                            }
                        }
                    }

                    @SuppressWarnings("unchecked")
                    @Override
                    public boolean step(IPointable result) throws HyracksDataException {
                        if (pos < tileValues.size()) {
                            aInt32.setValue(tileValues.get(pos));
                            resultStorage.reset();
                            intSerde.serialize(aInt32, resultStorage.getDataOutput());
                            result.set(resultStorage);
                            ++pos;
                            return true;
                        }
                        return false;
                    }
                };
            }
        };
    }
}
