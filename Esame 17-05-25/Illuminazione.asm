asm Illuminazione
import ../Libs/StandardLibrary

// *** Esame 25 Maggio 2017 ***
// Se è giorno, la luce non viene accesa. Se è notte, la luce viene accesa per 10 minuti appena viene aperto il cancello di casa. 
// In presenza di malfunzionamento, il sistema va in stato di errore. [pt. 5]

signature:
	domain Light subsetof Agent
	domain Controller subsetof Agent
	enum domain DayState = {DAY | NIGHT}
	enum domain LightState = {ON | OFF}
	
	dynamic monitored error : Boolean
	dynamic monitored dayState : DayState
	dynamic shared gateOpenPulse : Boolean
	dynamic monitored gateTimePassed : Boolean
	dynamic controlled lightsState : LightState
	dynamic controlled light : Light -> LightState
	
	static light1 : Light
	static light2 : Light
	static controller : Controller
	
definitions:
	rule r_Light = light(self) := lightsState
	
	rule r_Controller = 
		if (not(error)) then par
			if (lightsState = OFF and gateOpenPulse and dayState = NIGHT) then
				lightsState := ON
			endif
			if (lightsState = ON and gateTimePassed) then
				lightsState := OFF
			endif
			gateOpenPulse := false
		endpar endif
		
	main rule r_Main = par
		forall $light in Light do program($light)
		program(controller)
	endpar
	
default init s0:
	function gateOpenPulse = false
	function lightsState = OFF
	function light($l in Light) = OFF
	
	agent Light : r_Light[]
	agent Controller : r_Controller[]