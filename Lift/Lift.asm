asm Lift

import ../Libs/StandardLibrary

signature:
	domain Lift subsetof Agent
	domain Floor subsetof Integer
	enum domain Direction = {UP | DOWN}
	enum domain State = {HALTING | MOVING}
	dynamic shared hasToDeliverAt : Prod(Lift, Floor) -> Boolean
	dynamic shared existCallFromTo : Prod(Floor, Direction) -> Boolean
	dynamic controlled liftFloor : Lift -> Floor
	dynamic controlled liftDirection : Lift -> Direction
	dynamic controlled liftState : Lift -> State
	
	derived hasToVisit : Prod(Lift, Floor) -> Boolean
	derived attracted : Prod(Lift, Direction) -> Boolean
	derived canContinue : Lift -> Boolean

	static nextFloor : Prod(Floor, Direction) -> Floor	
	static inverse : Direction -> Direction
	
	static lift1 : Lift
	
definitions:
	domain Floor = {0 : 3}
	
	function nextFloor($floor in Floor, $dir in Direction) = 
		if ($dir = UP) then
			$floor + 1
		else
			$floor - 1
		endif
		
	function inverse($dir in Direction) = 
		if $dir = UP then DOWN else UP endif
	
	function hasToVisit($lift in Lift, $floor in Floor) = 
		hasToDeliverAt($lift, $floor) or
		existCallFromTo($floor, UP) or 
		existCallFromTo($floor, DOWN) 
		
	function attracted($lift in Lift, $dir in Direction) = 
		if ($dir = UP) then
			(exist $floor in Floor with $floor > liftFloor($lift) and hasToVisit($lift, $floor))
		else 
			(exist $floor1 in Floor with $floor1 < liftFloor($lift) and hasToVisit($lift, $floor1))
		endif
		
	function canContinue($lift in Lift) = 
		attracted($lift, liftDirection($lift))
		and not hasToDeliverAt($lift, liftFloor($lift))
		and not existCallFromTo(liftFloor($lift), liftDirection($lift))
	
	rule r_GoTo($dir in Direction) = par
		liftState(self) := MOVING
		liftFloor(self) := nextFloor(liftFloor(self), $dir)
		hasToDeliverAt(self, nextFloor(liftFloor(self), $dir)) := false
		existCallFromTo(nextFloor(liftFloor(self), $dir), $dir) := false
	endpar
	
	rule r_Stop = par
		liftState(self) := HALTING
		hasToDeliverAt(self, liftFloor(self)) := false
		existCallFromTo(liftFloor(self), liftDirection(self)) := false
	endpar
	
	// Rules
	rule r_Lift = 
		if (liftState(self) = HALTING) then
			if (attracted(self, liftDirection(self))) then
				r_GoTo[liftDirection(self)]
			else if (attracted(self, inverse(liftDirection(self)))) then par
				existCallFromTo(liftFloor(self), inverse(liftDirection(self))) := false
				r_GoTo[inverse(liftDirection(self))]
			endpar endif endif
		else
			if (canContinue(self)) then
				r_GoTo[liftDirection(self)]
			else
				r_Stop[]
			endif
		endif
	
	// Invariants
	
	// Main rule
	main rule r_Main =
		program(lift1)
	
// Default init
default init s0:
	function hasToDeliverAt($l in Lift, $f in Floor) = false
	function existCallFromTo($f in Floor, $d in Direction) = false
	function liftFloor($l in Lift) = 0
	function liftDirection($l in Lift) = UP
	function liftState($l in Lift) = HALTING
	
	// Agents
	agent Lift : r_Lift[]
	