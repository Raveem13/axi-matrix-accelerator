# AXI-Based Matrix Accelerator with UVM Verification

## Project Overview

This project implements a **parameterized AXI-based matrix computation accelerator** along with an **verification environment** using **SystemVerilog and UVM**.

The focus of this project is **verification-first design**, demonstrating how real-world silicon teams verify **control plane (AXI4-Lite)** and **data plane (AXI4-Stream)** interfaces, handle **backpressure**, build **reference models**, and achieve **coverage-driven closure**.

This repository reflects **end-to-end verification ownership**, from RTL bring-up to system-level UVM verification and regression readiness.

---

## Key Objectives

* Design a realistic AXI-based accelerator IP
* Verify **control plane and data plane independently and together**
* Build a **scalable, layered UVM testbench architecture**
* Demonstrate **debugging, coverage closure, and regression mindset**
* Follow **industry-aligned verification workflows**

---

## Architecture Overview

### 🔹 DUT Description

* Matrix computation accelerator (initially fixed size, upgradeable to **MxNxK**)
* Separate interfaces for:

  * **AXI4-Lite** → Control & configuration
  * **AXI4-Stream** → Matrix data input/output
* Internally uses:

  * FSM-based control logic
  * Parameterized MAC datapath
* Clean separation between **control path** and **datapath**

---
### 🔹 Block Diagram
![alt text](doc/images/01Architecture_Diagram.svg)

>The accelerator separates the control and data planes.

>The control plane configures matrix dimensions and start control,
while the data plane streams matrices and computation results.
---

### 🔹 Interfaces

| Interface            | Purpose                                |
| -------------------- | -------------------------------------- |
| AXI4-Lite            | Register access, configuration, status |
| AXI4-Stream (Input)  | Matrix input data stream               |
| AXI4-Stream (Output) | Computation result stream              |

---

## Project Phases (Project Evolution)

> **Note:**
> **Phases** describe how the project evolved over time.
> **Layers** are used later to describe verification abstraction.

---

### **Phase 1: Matrix Multiply Compute Core**

This phase focuses on **pure RTL design and local verification**, before introducing AXI protocols.

**Scope**

* Single MAC unit
* 2×2 MAC array
* 2×2×K MAC array
* M×N MAC array
* M×N×K parameterized design
* Separate **datapath and control FSM**
* Compile-time parameterization (sizes, widths)

**Structure of MAC Unit**

![alt text](doc/images/02_MAC_Unit.svg)

**Verification**

* Directed SystemVerilog testbench
* Cycle-accurate reference model
* Corner cases:

  * Zero matrices
  * Max/min values
  * Partial K accumulation
  * Reset mid-compute
* Assertions:

  * FSM safety
  * Accumulate enable correctness
  * Overflow / valid sequencing

![alt text](doc/images/02Compute_Architecture.svg)

---

### **Phase 2: AXI-Lite & AXI-Stream Wrapper Implementation**

This phase converts the compute core into a **usable AXI-based IP**.

**AXI-Lite (Control Plane)**

* Register map for:

  * Configuration
  * Start
  * Status / DONE
* Full channel handling:

  * AW / W / B
  * AR / R
* Proper VALID/READY handshakes
* Interrupt / DONE signaling

**AXI-Stream (Data Plane)**

* Matrix input streaming
* Output result streaming
* Burst handling
* Backpressure (`TREADY` toggling)
* Stress and corner scenarios

**Integration**

* Clean control ↔ datapath interaction
* No combinational protocol coupling
* Reset & idle safety

<!-- Todo: **Add diagram here:**

* System-level block diagram (CPU/PS → AXI-Lite → Control Wrapper → MAC Core) -->

---

### **Phase 3: UVM-Based Verification (Isolated Planes)**

This phase introduces **UVM verification**, with control and data planes verified independently.

#### Control Plane Verification (AXI4-Lite)

**Completed Features**

* Register read/write tests
* Reset behavior verification
* DONE/status register readback
* Invalid access handling
* FSM stability under random access

**Techniques**

* Directed tests + constrained-random sequences
* Protocol assertions
* Functional coverage for register fields

---

#### Data Plane Verification (AXI4-Stream)

**Completed Features**

* Random packet generation
* Variable packet sizes
* Backpressure injection (`TVALID` & `TREADY` toggling)
* Multi-monitor architecture:

  * Control-plane monitor
  * Data-plane monitor

**Key Point**

> Control and data planes operate on **different transaction types**, are monitored independently, and are correlated only at the scoreboard/reference model level.

---

### **Phase 4: System-Level Bring-Up UVM (Control + Data Together)**

This phase focuses on **end-to-end system verification**.

**What Happens**

* Control plane configures the DUT
* Data plane streams matrices
* Output is collected and checked end-to-end
* Reference model correlates:

  * Control transactions
  * Data transactions
* Virtual sequences coordinate both planes

**Stress Scenarios**

* Backpressure during active compute
<!-- * Reset mid-transaction -->
* Overlapping configuration and data
* Regression-safe system tests

---

## Verification Architecture (Layered Methodology)

The UVM testbench itself follows a **layered verification abstraction**:

| Layer   | Description                                      |
| ------- | ------------------------------------------------ |
| Layer 1 | RTL sanity, waveform-level debugging             |
| Layer 2 | Directed SystemVerilog tests                     |
| Layer 3 | UVM-based constrained-random verification        |
| Layer 4 | Coverage-driven verification                     |
| Layer 5 | Debugging, failure analysis & regression mindset |

---

## UVM Testbench Architecture

The verification environment follows a layered UVM architecture with
separate agents for control and data planes.

![alt text](doc/images/04UVM_tb_architecture.svg)

### Components Implemented

* UVM Environment
* Agents (Active / Passive)
* Sequencer and Driver
* Separate Monitors for control and data
* Scoreboard
* Cycle-accurate Reference Model
* Virtual Sequences
* Configuration Database usage
<!-- * Factory overrides -->

---

## 📊 Coverage

**Implemented Coverage**

* Register-level functional coverage
* FSM state coverage
* AXI handshake coverage
* Backpressure scenarios
* Packet length and boundary cases

Coverage is used as a **closure and guidance tool**, not as a checkbox.

<!-- Todo: **Add screenshot here (optional):** -->

* Functional coverage summary page
  <!-- Todo: **Link only (not embed):** -->
* `reports/r0x_system_cov/dashboard.html`

---

## Debugging & Failure Handling

This project explicitly focuses on **real-world verification failure modes**:

* False passes
* Phase misuse bugs
* Coverage blind spots
* Factory / config DB misuse
* Regression hygiene

This is treated as a **core learning and design goal**, not an afterthought.

---

## 🛠️ Tools & Technologies

* **Languages:** SystemVerilog, Verilog
* **Methodology:** UVM 1.2
* **Simulation:** XSIM (Vivado)
* **Waveform Debug:** GTKWave
* **Build & Scripts:** Bash, Tcl

For setting up Vivado on local machine, check this link:

https://github.com/Raveem13/VivadoXSIM-UVM_verification

---

## 📂 Repository Structure

```
axi_matrix_accelerator/
├── rtl/
│   ├── control/
│   ├── datapath/
│   └── top/
├── tb/
│   ├── interfaces/
│   ├── agents/
│   ├── env/
│   ├── sequences/
│   ├── tests/
│   └── scoreboard/
├── scripts/
├── reports/
│       └── r0x_system_cov/
├── docs/
└── README.md
```

---

## Current Status

✅ Control plane verification complete
✅ Data plane verification complete
✅ Random Stall & Backpressure testing complete
✅ Reference model & scoreboard complete
✅ Functional coverage implemented
✅ System-level UVM bring-up completed

<!-- ---

## Planned Enhancements

* Full M×N×K parameterization
* Additional stress regressions
* Performance counters
* Assertion-based coverage expansion -->

---

## Author

**Raveem Gouda**

---

⭐ Found this repo helpful? Give it a star to show your support and help others discover it too!

