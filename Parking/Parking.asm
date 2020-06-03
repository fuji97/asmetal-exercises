asm Parking
import ../Libs/StandardLibrary
import ../Libs/CTLlibrary

// *** Sistema di Parcheggio ***
// 
// Sono presenti due camere, una all'ingresso e una all'uscita di un parcheggio.
// Quando un'auto passa dalla camera, essa lo notifica al controllore che conta
// quante auto sono presenti nel parcheggio.
// Un semaforo mostra una luce verde se sono presenti posti, altrimenti rosso
// fino a quando non si libera un posto.

signature:
	domain Cars subsetof Integer
	enum domain CameraPosition = {ENTER | EXIT}
	enum domain Light = {RED | GREEN}
	
	dynamic controlled parkedCars : Cars
	dynamic monitored carPassed : CameraPosition -> Boolean
	dynamic out semaphoreLight : Light
	
	static maxCars : Cars
	
definitions:
	// Inzializzazioni statiche
	domain Cars = {0 : 10}
	function maxCars = 10
	
	// Regole
	rule r_CheckCameras =
		if (not (carPassed(ENTER) and carPassed(EXIT))) then
			if (carPassed(ENTER) and parkedCars < maxCars) then
				parkedCars := parkedCars + 1
			else if (carPassed(EXIT) and parkedCars > 0) then
				parkedCars := parkedCars - 1
			endif endif
		endif
		
	rule r_SetSemaphoreLight =
		if (parkedCars >= maxCars) then
			semaphoreLight := RED
		else
			semaphoreLight := GREEN
		endif
	
	// CTL
	CTLSPEC(ag(parkedCars >= 0 and parkedCars <= maxCars))
	CTLSPEC(ag(parkedCars = maxCars implies a(semaphoreLight = RED, carPassed(EXIT))))
	
	// Invarianti
	invariant over parkedCars : parkedCars >= 0 and parkedCars <= maxCars
	invariant over semaphoreLight : (parkedCars < maxCars and semaphoreLight = GREEN) xor (parkedCars = maxCars and semaphoreLight = RED)
	
	// Main rule
	main rule r_Main = seq
		r_CheckCameras[]
		r_SetSemaphoreLight[]
	endseq
	
default init s0:
	// Inizializzazioni dinamiche
	function parkedCars = 0
	function semaphoreLight = GREEN
