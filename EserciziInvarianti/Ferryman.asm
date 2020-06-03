asm Ferryman

import ../Libs/StandardLibrary

signature:
	enum domain Choice = {MOVE_WOLF | MOVE_GOAT | MOVE_CABBAGE | NOTHING}
	enum domain Guest = {WOLF | GOAT | CABBAGE}
	enum domain Side = {LEFT | RIGHT}
	controlled position : Guest -> Side
	monitored transport : Choice
	controlled ferryman : Side
	derived inverse : Side -> Side
	derived guestFromChoice : Choice -> Guest
	derived allRight : Boolean
	derived checkSide : Side -> Boolean
	out outMessage : String
	
definitions:
	function inverse($s in Side) =
		switch $s
			case LEFT: RIGHT
			case RIGHT: LEFT
		endswitch
		
	function guestFromChoice($c in Choice) =
		switch $c
			case MOVE_WOLF : WOLF
			case MOVE_GOAT : GOAT
			case MOVE_CABBAGE : CABBAGE
		endswitch
		
	function allRight = 
		if position(WOLF) = RIGHT and position(GOAT) = RIGHT and position(CABBAGE) = RIGHT then
			true
		else
			false
		endif
		
	function checkSide($side in Side) = 
		if (position(WOLF) = $side and position(GOAT) = $side) or
		   (position(GOAT) = $side and position(CABBAGE) = $side) then
		   	false
		else
			true
		endif
		
	rule r_Transport = par
		if transport != NOTHING then
			position(guestFromChoice(transport)) := inverse(position(guestFromChoice(transport)))
		endif
		ferryman := inverse(ferryman)
	endpar
	
	invariant over transport, ferryman : transport = NOTHING or ferryman = position(guestFromChoice(transport))
	invariant over ferryman, position : checkSide(inverse(ferryman))
	
	main rule r_Main =
		if not allRight then
			seq
				r_Transport[]
				if allRight then
					outMessage := "You win!"
				endif
			endseq
		endif
	
default init s0:
	function ferryman = LEFT
	function position($g in Guest) = LEFT
	function outMessage = "Playing..."
	
		