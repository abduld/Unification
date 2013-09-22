

BeginPackage["Unification`"]

Unify;
UnifyObject;

substitute;

Variable;
Term;

Begin["`Private`"]


occurs[x_, Variable[y_]] :=
	x === y
occurs[x_, Term[h_, r_]] :=
	MemberQ[occurs[x, #]& /@ r, True]

unifyOne[x_Integer, y_Variable] :=
	y -> x
unifyOne[x_Variable, y_Integer] :=
	x -> y
unifyOne[x_Variable, y_Variable] :=
	If[x === y,
		{},
		x -> y
	]
unifyOne[Term[ha_, ra_], Term[hb_, rb_]] :=
	{}
unifyOne[x_Integer, y_Integer] :=
	If[x == y,
		{},
		Throw[
			Print["ERROR: Failed to unify ", x, " ", y];
			$Failed
		]
	]
	
substitute[s_, x_, Variable[y_]] :=
	If[x === y,
		s,
		Variable[y]
	]
substitute[s_, x_, Term[f_, u_]] :=
	Term[f, substitute[s, x, #]& /@ u]
	
applySubstitution[s_, t_, g_] :=
	Fold[
		Function[{x, u}, substitute[u, x, g]],
		s,
		t
	]

unify[{}] := {}
unify[{{x_, y_}, rest___}] := Module[{t2, t1},
	t2 = unify[{rest}];
	t1 = unifyOne[applySubstitution[t2, x], applySubstitution[t2, y]];
	
]

End[]

EndPackage[]

