### Accelerator Overview

* Fixed 4×4 matrix multiply
* Blocking / tiling for 8×8, 16×16 matrices
* Deterministic execution

### Datapath

* 16 MAC units
* Accumulator per output
* Local scratchpad (ping–pong)

### Control FSM

States:

```
IDLE → LOAD → COMPUTE → STORE → DONE
```

### AXI Interfaces

* AXI4-Lite: control/status
* AXI4-Full: DMA for A, B, C

### Register Map (Freeze this)

| Offset | Name   | Description      |
| ------ | ------ | ---------------- |
| 0x00   | CTRL   | bit0 = start     |
| 0x04   | SIZE   | matrix dimension |
| 0x08   | A_BASE | base addr        |
| 0x0C   | B_BASE | base addr        |
| 0x10   | C_BASE | base addr        |
| 0x14   | STATUS | done             |

---