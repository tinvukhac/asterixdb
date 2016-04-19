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
package org.apache.asterix.runtime.operators.joins;

import org.apache.asterix.dataflow.data.nontagged.serde.AIntervalSerializerDeserializer;
import org.apache.hyracks.api.comm.IFrameTupleAccessor;
import org.apache.hyracks.api.exceptions.HyracksDataException;
import org.apache.hyracks.dataflow.std.buffermanager.ITupleAccessor;

public class IntervalJoinUtil {

    public static long getIntervalStart(IFrameTupleAccessor accessor, int tupleId, int fieldId)
            throws HyracksDataException {
        int start = accessor.getTupleStartOffset(tupleId) + accessor.getFieldSlotsLength()
                + accessor.getFieldStartOffset(tupleId, fieldId) + 1;
        long intervalStart = AIntervalSerializerDeserializer.getIntervalStart(accessor.getBuffer().array(), start);
        return intervalStart;
    }

    public static long getIntervalEnd(IFrameTupleAccessor accessor, int tupleId, int fieldId)
            throws HyracksDataException {
        int start = accessor.getTupleStartOffset(tupleId) + accessor.getFieldSlotsLength()
                + accessor.getFieldStartOffset(tupleId, fieldId) + 1;
        long intervalEnd = AIntervalSerializerDeserializer.getIntervalEnd(accessor.getBuffer().array(), start);
        return intervalEnd;
    }

    public static long getIntervalStart(ITupleAccessor accessor, int fieldId) throws HyracksDataException {
        int start = accessor.getTupleStartOffset() + accessor.getFieldSlotsLength()
                + accessor.getFieldStartOffset(fieldId) + 1;
        long intervalStart = AIntervalSerializerDeserializer.getIntervalStart(accessor.getBuffer().array(), start);
        return intervalStart;
    }

    public static long getIntervalEnd(ITupleAccessor accessor, int fieldId) throws HyracksDataException {
        int start = accessor.getTupleStartOffset() + accessor.getFieldSlotsLength()
                + accessor.getFieldStartOffset(fieldId) + 1;
        long intervalEnd = AIntervalSerializerDeserializer.getIntervalEnd(accessor.getBuffer().array(), start);
        return intervalEnd;
    }

}