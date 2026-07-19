
all: build check

build:
	lake build

FMT_TARGETS=GraphQL.lean Tests.lean Lint.lean GraphQL Tests

check:
	lake lint
	lake exe fmt --check --recursive $(FMT_TARGETS)

fmt:
	lake exe fmt --recursive $(FMT_TARGETS)
