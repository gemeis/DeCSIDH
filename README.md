The benchmarks can be copied and are ready to use. The file `csidh.m` is a slight modification of the original file from https://velusqrt.isogeny.org/software.html.

To start, load either of the parameter sets:
``
magma load_csidh512.m
magma load_csidh1792.m
magma load_csidh4096.m
``
which will also load `csidh.m` and the benchmark routines from `delegate_new.m`.

Then within magma, run the command
`` benchmark_CSIDH(delta,N); ``
or 
`` benchmark_ID(delta,N); ``
to benchmark CSIDH or the ID protocol underlying SeaSign with the loaded parameter set for a specific delta with N iterations. The case delta=0 represents the asymptotic limit delta->infinity.

To speed up the benchmarks, the server computations are left out. Note that this makes the benchmarks only representative and the actual output incorrect. To include the server computations simply run the commands 
`` benchmark_CSIDH(delta,N : server:=true); ``
or 
`` benchmark_ID(delta,N  : server:=true); ``
which also tests for correctness of the delegation procedure by comparing it to the local computation. In this case, correctness can be shown. We warn however, that for large delta and high parameter sets, these benchmarks can however become quite slow.
