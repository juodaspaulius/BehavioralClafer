open util/ordering[Time] 
sig Time {loop: lone Time}
fact Loop {loop in last -> Time}
enum State { alive, dead }
sig Person {
	age: Int one -> Time,
	state: State -> Time
} {
	all a: age.Time | a > 0
}
// G[ X [next(age)>=age] ])
pred ageOnlyIncreases [t: Time] {
	let nt = (Time <: next+loop) | // next time
		all p:Person | // constraint context
			some loop and all t': t.*nt | // G
				let t''=t'.nt | let a = p.age | some t'' and a.t' <= a.t''
}
// alive U dead 
pred aliveUntilDead[t: Time]{
	let nt = (Time <: next+loop) | // next time
		all p: Person | 
			some t' : t.*nt | p.state.t' = dead and  // eventually dead 
				all t'' : t.*nt & ^nt.t' | p.state.t'' = alive // but before that is alive
}
// G ( dead -> G(dead)) 
pred onceDeadAlwaysDead[t: Time]{
	let nt = (Time <: next+loop) | // next time
		all p: Person |
			some loop and all t': t.*nt |  // first G
				(p.state.t' = dead) implies some loop and all t'': t'.*nt | // implication and second G
					p.state.t''=dead
}
// Bind all predicates to initial Time
fact { all t: Time <: first | 
	aliveUntilDead[t] && onceDeadAlwaysDead[t] && ageOnlyIncreases[t] 
}
pred show{}
run show for exactly 10 Time, exactly 4 Person
