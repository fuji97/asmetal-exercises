//Ruota della fortuna: La ruota ha 37 caselle numerate nell'intervallo [0, 36]. 
//Ogni casella ha un colore: verde: lo 0; rosso: i numeri pari tranne lo 0; nero: i numeri dispari.
//La macchina in modo casuale deve scegliere un numero in [0, 36]; l'utente deve poter scegliere un numero in [0, 36].
//Sia l'utente, sia il banco dispongono di un budget: all'inizio entrambi hanno 5 euro.
//Dopo ogni giocata, il budget dell'utente e del banco devono essere aggiornati a seconda del vincitore:
//-se l'utente indovina il numero incassa 2 euro, e il banco perde 2 euro;
//-se l'utente non indovina il numero, ma il numero scelto è dello stesso colore di quello uscito sulla ruota, incassa 1 euro, e il banco perde 1 euro;
//-se l'utente non indovina nè il numero nè il colore perde 1 euro, e il banco incassa 1 euro.


asm ruotaFortuna

import LIB/StandardLibrary
import LIB/CTLlibrary

signature:
	domain Number subsetof Integer
	domain Budget subsetof Integer
	enum domain Win={NUMERO|COLORE|PERDE}
	enum domain Color={VERDE|ROSSO|NERO}
	enum domain Player={BANCO|UTENTE}
	
	controlled color: Color
	controlled budget: Player->Budget
	controlled choosedNumber: Player->Number
	controlled winner: Player
	
	derived colorNumber: Number -> Color
	derived finalWinner: Player

definitions:
	domain Number= {0 : 36}
	domain Budget= {0 : 10}

	function colorNumber($n in Number)=
		if $n=0 then VERDE else
			if $n>1 and ($n mod 2)=0 then ROSSO else NERO endif endif
			
	function finalWinner=
		if budget(UTENTE)=10 then UTENTE else if budget(BANCO)=10 then BANCO else undef endif endif
	
	rule r_win($w in Win)=
		par
			if $w=NUMERO then
				par
					budget(UTENTE):=budget(UTENTE)+2
					budget(BANCO):=budget(BANCO)-2
				endpar
			endif
			if $w=COLORE then
				par
					budget(UTENTE):=budget(UTENTE)+1
					budget(BANCO):=budget(BANCO)-1
				endpar
			endif		
			if $w=PERDE then
				par
					budget(UTENTE):=budget(UTENTE)-1
					budget(BANCO):=budget(BANCO)+1
				endpar
			endif
		endpar

	rule r_game=
		choose $n in Number with true do
			choose $u in Number with true do
			par	
				choosedNumber(BANCO):=$n
				choosedNumber(UTENTE):=$u
				if $n=$u then
					r_win[NUMERO]
				else
					if colorNumber($n)=colorNumber($u) then
						r_win[COLORE]
					else
						r_win[PERDE]
					endif
				endif
			endpar

	invariant over budget: budget(UTENTE)+budget(BANCO)=10
	//nel sistema ci sono globalmente 10 euro
	CTLSPEC ag(budget(UTENTE)+budget(BANCO)=10)
	//il banco può avere da 0 a 10 euro
	CTLSPEC ef(budget(BANCO)>=0 and budget(BANCO)<=10)
	//in ogni caso il banco avrà sempre un budget tra 0 e 10 euro
	CTLSPEC ag(budget(BANCO)>=0 and budget(BANCO)<=10)
	//se il giocatore perde tutti i soldi non li recupera più
	CTLSPEC ag(budget(UTENTE)=0 implies ag(budget(UTENTE)=0))

main rule r_main=
	if isUndef(finalWinner) then
		r_game[]
	else
		winner:=finalWinner
	endif

default init s0:
	function budget($p in Player)=5
