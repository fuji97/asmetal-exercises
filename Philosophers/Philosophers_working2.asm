asm Philosophers_working2
import ../Libs/StandardLibrary
import ../Libs/CTLlibrary

// Versione nella quale, per evitare il deadlock, il filosofo prende entrambe le forchette 
// contemporaneamente o nessuna.
// Questa versione è più corretta delle precedenti ma prevede che il sistema possa bloccare
// due risorse in un solo passo.

signature:
	domain Philosopher subsetof Agent
	abstract domain Fork
	enum domain State = {THINKING | EATING}
	
	dynamic controlled owner : Fork -> Philosopher
	dynamic controlled state : Philosopher -> State
	dynamic monitored hungry : Philosopher -> Boolean
	
	derived hasAllForks : Philosopher -> Boolean
	derived deadlock : Boolean
	derived isFree : Fork -> Boolean
	derived safeCondition : Philosopher -> Boolean
	
	static leftFork : Philosopher -> Fork
	static rightFork : Philosopher -> Fork
	
	static philosopher1 : Philosopher
	static philosopher2 : Philosopher
	static philosopher3 : Philosopher
	static philosopher4 : Philosopher
	
	static fork1 : Fork
	static fork2 : Fork
	static fork3 : Fork
	static fork4 : Fork
	
	static useSafeCondition : Boolean
	
definitions:
	// Inizializzazioni statiche 
	function useSafeCondition = true	// Disabilitando questa variabile il sistema può entrare in deadlock
	
	function leftFork($phi in Philosopher) = switch $phi
		case philosopher1 : fork1
		case philosopher2 : fork2
		case philosopher3 : fork3
		case philosopher4 : fork4
	endswitch
	
	function rightFork($phi in Philosopher) = switch $phi
		case philosopher1 : fork2
		case philosopher2 : fork3
		case philosopher3 : fork4
		case philosopher4 : fork1
	endswitch
	
	function hasAllForks($phi in Philosopher) = owner(leftFork($phi)) = $phi and owner(rightFork($phi)) = $phi
	function isFree($fork in Fork) = isUndef(owner($fork))
	function safeCondition($phi in Philosopher) = 
		// Let non supportato da NuSMV
		//let ($left=owner(leftFork($phi)), $right=owner(rightFork($phi))) in
		//	(isUndef($left) or $left = $phi) and (isUndef($right) or $right = $phi)
		//endlet
		(isFree(leftFork($phi)) or owner(leftFork($phi)) = $phi) and (isFree(rightFork($phi)) or owner(rightFork($phi)) = $phi)
	function deadlock = not(exist $phi in Philosopher with state($phi) != EATING or hasAllForks($phi)) and not(exist $fork in Fork with isFree($fork))
	
	// Regole
	rule r_TakeForks($phi in Philosopher) = par
		if (isFree(leftFork($phi))) then
			owner(leftFork($phi)) := $phi
		endif
		if (isFree(rightFork($phi))) then
			owner(rightFork($phi)) := $phi
		endif
	endpar
	
	rule r_ReleaseForks($phi in Philosopher) = par
		if (owner(leftFork($phi)) = $phi) then owner(leftFork($phi)) := undef endif
		if (owner(rightFork($phi)) = $phi) then owner(rightFork($phi)) := undef endif
	endpar
		
	rule r_Eat($phi in Philosopher) = par
		state($phi) := EATING
		if (safeCondition($phi) or not(useSafeCondition)) then
			r_TakeForks[$phi]
		endif
	endpar
	
	rule r_Think($phi in Philosopher) = par
		state($phi) := THINKING
		r_ReleaseForks[$phi]
	endpar
	
	rule r_Eating($phi in Philosopher) =
		if (hasAllForks($phi)) then 
			r_Think[$phi]
		else
			r_Eat[$phi]
		endif
		
	rule r_Thinking($phi in Philosopher) =
		if (hungry($phi)) then
			r_Eat[$phi]
		endif
		
	rule r_Philosopher =
		if (state(self) = EATING) then
			r_Eating[self]
		else
			r_Thinking[self]
		endif
	
	// CTL
	// Disabilitando la safe condition, entrambe le CTL falliscono
	CTLSPEC(not(ef(deadlock)))
	CTLSPEC(ag(state(philosopher1) = EATING implies ef(state(philosopher1) = THINKING)))
	
	// Invarianti
	invariant over owner : not(deadlock)
	
	// Main Rule
	main rule r_Main = 
		choose $phi in Philosopher with true do program($phi)
		//seq
			//program(philosopher1)
			//program(philosopher2)
			//program(philosopher3)
			//program(philosopher4)
		//endseq
	
default init s0:
	// Inizializzazioni dinamiche
	function state($phi in Philosopher) = THINKING
	function owner($fork in Fork) = undef
	
	// Agenti
	agent Philosopher : r_Philosopher[]