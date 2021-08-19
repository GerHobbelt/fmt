$(eval $(begin-module))

################################################################
# unit definitions
################################################################

module_units_h := args chrono color compile core format format-inl
module_units_h += locale os ostream printf ranges xchar

# note: renamed format.cc to format.cpp, etc., for use with makefile
module_units_cpp-h := format os
# note: no C++20 module support in ndmakefile yet
# module_units_cpp := fmt
# module_units_f :=

module_programs_cpp :=
# module_programs_f :=
# module_generated :=

################################################################
# library creation flag
################################################################

$(eval $(library))

################################################################
# special variable assignments, rules, and dependencies
################################################################

$(eval $(end-module))
