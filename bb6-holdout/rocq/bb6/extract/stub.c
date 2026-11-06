/* The checker never converts ints to floats; this only satisfies a link reference in the kernel's uint63.ml. */
#include <caml/mlvalues.h>
#include <caml/alloc.h>
value coq_uint63_to_float(value x) { return caml_copy_double((double)(unsigned long)Long_val(x)); }
value coq_uint63_to_float_byte(value x) { return coq_uint63_to_float(x); }
double coq_uint63_to_float_unboxed(value x) { return (double)(unsigned long)Long_val(x); }
