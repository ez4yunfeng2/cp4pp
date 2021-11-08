file = 

all:
	@clang++ -g -O3 cp4pp.cpp `llvm-config --cxxflags --ldflags --system-libs --libs all` -o cp4pp
	@./cp4pp $(file)
	@clang++ main.cpp output.o -o main
	@./main

exec:
	@./cp4pp $(file)
	@clang++ main.cpp output.o -o main
	@./main

build:
	@clang++ -g -O3 cp4pp.cpp `llvm-config --cxxflags --ldflags --system-libs --libs all` -o cp4pp