asm AirConditioner
import ../Libs/StandardLibrary

// *** ESAME: Air Conditioner ***
//
// Modellare con le ASM multi-agenti il comportamento del
// seguente sistema di condizionamento. Il sistema è composto
// da un controllore e da una condizionatore.
// In fase giorno, il controllore invia il comando di accensione al
// condizionatore se la temperatura ambiente supera il valore
// settato dall’utente. Per default la temperatura ambiente è
// fissata a 26°, ma l’utente può cambiare a piacere questo
// valore. Il condizionatore viene spento quando arriva in
// temperatura.
// In fase notte, il controllore invia al condizionatore un comando
// di accensione se la temperatura è superiore ad un valore
// minimo. Tale valore è fissato per default a 28°.
// Un eventuale guasto del condizionatore, mette l’intero sistema
// in una situazione di guasto.

signature:
	domain Conditioner subsetof Agent
	domain Controller subsetof Agent
	enum domain DayTime = {DAY | NIGHT}
	enum domain State = {ON | OFF}
	
	dynamic monitored daytime : DayTime
	dynamic monitored temp : Integer
	dynamic monitored error : Boolean
	dynamic controlled state : Conditioner -> State
	dynamic controlled onSignal : Conditioner -> Boolean
	dynamic shared threshold : DayTime -> Integer
	
	derived thresholdBypassed : Boolean
	
	static controller : Controller
	static conditioner : Conditioner

definitions:
	// Inizializzazioni statiche
	function thresholdBypassed = temp > threshold(daytime)
	
	// Regole
	rule r_Controller =
		if (not error) then
			if (thresholdBypassed and not onSignal(conditioner) and state(conditioner) = OFF) then
			 	onSignal(conditioner) := true
			endif
		endif
	
	rule r_Conditioner = 
		if (not error) then
			if (onSignal(self) = true) then par
				onSignal(self) := false
				state(self) := ON
			endpar endif
		else
			state(self) := OFF
		endif
	
	// Invarianti
	
	// Main rule
	main rule r_Main = par
		program(controller)
		program(conditioner)
	endpar
	
	default init s0:
		// Inizializzazioni dinamiche
		function threshold($daytime in DayTime) = if ($daytime = DAY) then 26 else 28 endif
		function onSignal($cond in Conditioner) = false
		function state($cond in Conditioner) = OFF
	
	// Agenti
	agent Controller : r_Controller[]
	agent Conditioner : r_Conditioner[]
	