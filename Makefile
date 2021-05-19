all: build

build: 
	@dune build @all

install:
	@dune install 

clean:
	@dune clean
