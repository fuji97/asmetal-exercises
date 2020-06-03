asm ControlSystem
import ../Libs/StandardLibrary
import ../Libs/CTLlibrary

// *** Esercizio esame ***
// Specificare un modello ASM per il seguente sistema di controllo. Il sistema di controllo è costituito
// da una coppia di attuatori collegati ad un computer. Ciascun attuatore può avere stato off oppure on. 
// Il computer controlla la sequenza degli stati degli attuatori emettendo i segnali OffPulse (= vai a off) 
// e OnPulse (= vai a on) a cui gli attuatori rispondono cambiando di stato. Il funzionamento degli 
// attuatori è controllato dal computer in base al seguente ciclo fisso di quattro fasi: fase1, dalle ore 20:00 alle 
// ore 08:00 del giorno successivo, entrambi gli attuatori sono in stato off; fase2, dalle ore 08:00 alle 
// ore 12:00 un attuatore è in off e l’altro è in on; fase3, dalle ore 12:00 alle ore 14:00 entrambi gli 
// attuatori sono in off nuovamente; fase4, dalle ore 14:00 alle ore 20:00 l’attuatore che prima era in 
// on rimane a off mentre l’altro passa a on. Ed il ciclo si ripete

signature:
	domain Controller subsetof Agent
	domain Actuator subsetof Agent
	enum domain Time = {TA | TB | TC | TD}
	enum domain State = {ON | OFF}
	dynamic monitored time : Time
	dynamic controlled state : Actuator -> State
	dynamic controlled timeState : Controller -> Time
	dynamic controlled offPulse : Actuator -> Boolean
	dynamic controlled onPulse : Actuator -> Boolean
	
	static controller : Controller
	static actuator1 : Actuator
	static actuator2 : Actuator
	
definitions:
	// Inizializzazioni statiche
	
	// Regole
	rule r_Actuator =
		if (offPulse(self)) then par
			offPulse(self) := false
			state(self) := OFF
		endpar else if (onPulse(self)) then par
			onPulse(self) := false
			state(self) := ON
		endpar endif endif
		
	rule r_SetOn($act in Actuator) = if (not(onPulse($act))) then onPulse($act) := true endif
	
	rule r_SetOff($act in Actuator) = if (not(offPulse($act))) then offPulse($act) := true endif
		
	rule r_Controller =
		if (timeState(self) != time) then par
			timeState(self) := time
			switch time
				case TA : par r_SetOff[actuator1] r_SetOff[actuator2] endpar
				case TB : par r_SetOn[actuator1] r_SetOff[actuator2] endpar
				case TC : par r_SetOff[actuator1] r_SetOff[actuator2] endpar
				case TD : par r_SetOff[actuator1] r_SetOn[actuator2] endpar
			endswitch
		endpar endif
	
	// CTLSPEC
	CTLSPEC(not(ef(state(actuator1) = ON and state(actuator2) = ON)))
	
	// Invarianti
	invariant over offPulse, onPulse : (forall $act in Actuator with not(offPulse($act) and onPulse($act)))
	
	// Main rule
	main rule r_Main = par
		program(controller)
		forall $act in Actuator with true do program($act) 
	endpar
	
	// Definizioni statiche
default init s0:
	function state($act in Actuator) = OFF
	function offPulse($act in Actuator) = false
	function onPulse($act in Actuator) = false
	
	// Agenti
	agent Controller : r_Controller[]
	agent Actuator : r_Actuator[]