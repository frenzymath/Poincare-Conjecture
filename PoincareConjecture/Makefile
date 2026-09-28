.PHONY: check contracts lean endpoint-axioms comparator-build comparator-setup comparator-source-check comparator

LEAN_BUILD ?= lake build
LEAN_CHECK ?= lake env lean
LEAN_TARGETS ?=

check: contracts lean
	$(LEAN_CHECK) scripts/check_poincare_endpoints.lean

contracts:
	python3 scripts/check_frozen_contracts.py

lean:
	$(LEAN_BUILD) $(LEAN_TARGETS)

endpoint-axioms:
	$(LEAN_BUILD) PoincareLib.Topology.Manifold.Poincare
	$(LEAN_CHECK) scripts/check_poincare_endpoints.lean

comparator-source-check:
	python3 comparator/check.py

comparator-build: comparator-source-check
	$(LEAN_BUILD) Challenge @Comparator/comparator @lean4export/lean4export

comparator-setup:
	python3 comparator/setup.py

comparator:
	bash comparator/run.sh
