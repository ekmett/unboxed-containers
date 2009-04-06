run: Benchmark
	./Benchmark

Benchmark: Data/Set/Unboxed.hs Benchmark.hs Makefile
	ghc --make Benchmark -O2 -fdicts-cheap 

clean: 
	rm -f Benchmark.hi Benchmark.o Benchmark Data/Set/Unboxed.hi Data/Set/Unboxed.o

.PHONY: clean
