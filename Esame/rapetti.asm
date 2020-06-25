asm rapetti
import ../Libs/StandardLibrary
import ../Libs/CTLlibrary

signature:
	domain AlphabetNumber subsetof Integer
	domain Point subsetof Integer
	enum domain A = {CF | CE | CD | CR | CI | CC | CO | CA | CP | CT}
	enum domain Result = {PC | USER | PATTA}
	static number : A -> AlphabetNumber
	
	dynamic controlled choosed : A -> Boolean
	dynamic monitored userChoice : A
	dynamic controlled userNumber : AlphabetNumber
	dynamic controlled pcNumber : AlphabetNumber
	
	dynamic controlled userPoints : Point
	dynamic controlled pcPoints : Point
	dynamic out winner : Result
	
	derived allChoosed : Boolean
	//derived pcChoose : AlphabetNumber
	
definitions:
	domain AlphabetNumber = {1 : 26}
	domain Point = {0 : 52}
	
	function number($a in A) = switch $a
		case CF : 6
		case CE : 5
		case CD : 4
		case CR : 18
		case CI : 9
		case CC : 3
		case CO : 15
		case CA : 1
		case CP : 17
		case CT : 20
	endswitch
	
	function allChoosed = (forall $a in A with choosed($a))
	
	rule r_Play($user in A, $pc in AlphabetNumber) = 
		if (not(choosed($user))) then
			par
				choosed($user) := true
				userNumber := number($user)
				pcNumber := $pc
				if (number($user) > $pc) then
					userPoints := userPoints + 2
				else if ($pc > number($user)) then
					pcPoints := pcPoints + 2
				else par
					userPoints := userPoints + 1
					pcPoints := pcPoints + 1
				endpar 
			 	endif endif
			 endpar
	 	endif
	 
	 CTLSPEC(ef(allChoosed))
	 CTLSPEC(ag(not(allChoosed and userPoints + pcPoints = 0)))
	 CTLSPEC(ag(ef(winner = PC or winner = USER or winner = PATTA)))
	
	main rule r_Main =
		if (allChoosed) then
			if (userPoints > pcPoints) then
				winner := USER
			else if (pcPoints > userPoints) then
				winner := PC
			else
				winner := PATTA
			endif endif
		else
			choose $i in AlphabetNumber with true do
				r_Play[userChoice, $i]
		endif
		
default init s0:
	function userPoints = 0
	function pcPoints = 0
	function choosed($a in A) = false
			
		
	