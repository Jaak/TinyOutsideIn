# Tiny OutsideIn(X)

This is a simple reference implementation of
[OutsideIn(X)](http://research.microsoft.com/apps/pubs/default.aspx?id=162516)
type inference algorithm. The language supports size constaints but is
otherwise **extremely** limited:
* No parser -- only abstract syntax.
* No evaluator.
* We assume that top-level bindings have types provided for them.
* No generalization of either let-expressions or top-level functions. However,
  that should not be too difficult to add.
* The inference algorithm only produces a system of constaints. No attempts
  have been made to solve them.
* Poorly documented and lazily coded (this really should be fixed).
