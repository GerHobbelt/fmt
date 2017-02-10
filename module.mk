$(eval $(begin-module))

################################################################
# unit definitions
################################################################

module_units_h := string time
module_units_cpp-h := format ostream posix printf  # note: renamed format.cc to format.cpp, etc., for use with makefile
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
