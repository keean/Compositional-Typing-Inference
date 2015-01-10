all: infer

clean:
	rm -f infer

infer: infer.cpp Parser-Combinators/parser_combinators.hpp
	clang++ ${CFLAGS} -ggdb -march=native -O3 -flto -std=c++11 -o infer infer.cpp
