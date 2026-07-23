
all: build check

build:
	time lake build

FMT_TARGETS=*.lean GraphQL Tests Lint

check:
	time lake lint
	time lake exe fmt --check --recursive $(FMT_TARGETS)

fmt:
	time lake exe fmt --recursive $(FMT_TARGETS)
