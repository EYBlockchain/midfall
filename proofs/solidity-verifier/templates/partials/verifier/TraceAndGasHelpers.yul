            {%- if self.trace %}
            // Trace builds emit u256 values through a planned scratch slot.
            // The topic is the stable trace ID used by Rust/Solidity fixture
            // comparison; the data word is the observed scalar.
            function trace_u256(id, value) {
                mstore(TRACE_U256_MPTR, value)
                log1(TRACE_U256_MPTR, 0x20, id)
            }
            // Trace G1 points as their 128-byte EIP-2537 memory slot.
            function trace_point(id, mptr) {
                log1(mptr, 0x80, id)
            }
            {%- endif %}
            {%- if self.gas_checkpoints %}
            // Section-boundary gas-attribution checkpoint. Emits a
            // single LOG1 (no data) with topic = (id << 248) | gas().
            // Cost: 375 (LOG base) + 375 (1 topic) = 750 gas/call.
            // Host-side parses the topic into (id, gas_left) and prints
            // pairwise deltas (see `dump_gas_checkpoints`).
            function gas_checkpoint(id) {
                log1(0, 0, or(shl(248, id), gas()))
            }
            {%- endif %}
