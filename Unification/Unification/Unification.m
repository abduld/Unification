

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

unifyOne[Variable[x_], Variable[y_]] :=
	If[x === y,
		{},
		{{x, Variable[y]}}
	]
unifyOne[Term[ha_, ra_], Term[hb_, rb_]] :=
	If[ha === hb && Length[ra] === Length[rb],
		First@MapThread[unify[{{##}}]&, {ra, rb}],
		Throw[
			Print["Failed: unable to unify in unifyOne"];
			$Failed
		]
	]
unifyOne[t_Term, x_Variable] :=
	unifyOne[x, t]
unifyOne[Variable[x_], t_Term] :=
	If[occurs[x, t],
		Throw[
			Print["Failed: cyclic unification"];
			$Failed
		],
		{{x, t}}
	]

substitute[s_, {x_, Variable[y_]}] :=
	If[x === y,
		s,
		Variable[y]
	]
substitute[s_, {x_, Term[f_, u_]}] :=
	Term[f, substitute[s, {x, #}]& /@ u]
	
applySubstitution[s_, t_] :=
	Fold[
		substitute,
		t,
		s
	]

Unify[args___] := Catch[
	unify[args]
]

unify[{}] := {}
unify[{{x_, y_}, rest___}] := Module[{t2, t1},
	t2 = unify[{rest}];
	t1 = unifyOne[applySubstitution[t2, x], applySubstitution[t2, y]];
	Join[t1, t2]
]

End[]

EndPackage[]

