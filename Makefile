all: infer

clean:
	rm -r infer

infer: infer.cpp Parser-Combinators/parser_combinators.hpp
	clang++ -ggdb -march=native -O3 -flto -std=gnu++11 -IParser-Combinators -o infer infer.cpp 
