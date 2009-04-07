run: Benchmark
	./Benchmark

Data/Set/UnboxedInstances.hs: instances.pl
	./instances.pl > Data/Set/UnboxedInstances.hs
	touch Data/Set/Unboxed.hs

Benchmark: Data/Set/Unboxed.hs Benchmark.hs Makefile Data/Set/UnboxedInstances.hs
	/usr/bin/time -a -p ghc --make Benchmark -O2 -fdicts-cheap 

clean: 
	rm -f Benchmark.hi Benchmark.o Benchmark Data/Set/Unboxed.hi Data/Set/Unboxed.o Data/Set/UnboxedInstances.hs

.PHONY: clean
