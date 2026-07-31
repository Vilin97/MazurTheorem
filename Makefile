.PHONY: setup build build-challenges quality check site-check

setup:
	lake exe cache get

build:
	LEAN_NUM_THREADS=1 lake build MazurTorsion

build-challenges:
	LEAN_NUM_THREADS=1 lake build Challenge

quality:
	python3 scripts/quality.py

check: quality build-challenges build

site-check:
	cd site && npm ci && npm run lint && npm run build
