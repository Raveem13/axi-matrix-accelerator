puts "Starting XSIM (Vivado TCL mode)..."

# Collect files correctly (NO **)
set RTL_FILES [glob rtl/*.sv]
set TB_FILES  [glob tb/*.sv]

# Compile
xvlog -sv $RTL_FILES $TB_FILES

# Elaborate
xelab work.basic_tb -debug typical

# Simulate
xsim work.basic_tb -runall

puts "Simulation complete."
