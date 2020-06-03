asm MorraCinese

import ../Libs/StandardLibrary

signature:
	enum domain Play = {SASSO | CARTA | FORBICE}
	enum domain Result = {USER | CPU | PATTA}
	static winner : Prod(Play, Play) -> Result
	dynamic controlled cpuPlay : Play
	dynamic monitored userPlay : Play
	dynamic out playResult : String
	dynamic monitored maxPlays : Integer
	dynamic controlled currentPlays : Integer
	dynamic out userWins : Integer
	dynamic out cpuWins : Integer
	
definitions:
	function winner($user in Play, $cpu in Play) =
		if not ($user = $cpu ) then
			switch ($user, $cpu ) 
				case (SASSO, FORBICE):
					USER
				case (CARTA, SASSO):
					USER
				case (FORBICE, CARTA):
					USER
				otherwise
					CPU
			endswitch
		else	
			PATTA
		endif
			
	main rule r_Main =
		if currentPlays < maxPlays or userWins = cpuWins then
			choose $cpu in Play with true do
				par
					currentPlays := currentPlays + 1
					cpuPlay := $cpu
					switch winner(userPlay, $cpu )
						case USER:
							par
								playResult := "Hai vinto"
								userWins := userWins + 1
							endpar
						case CPU:
							par
								playResult := "Ha vinto la CPU"
								cpuWins := cpuWins + 1
							endpar
						case PATTA:
							playResult := "Pareggio"
					endswitch
				endpar
		else
			playResult := "Fine partita"
		endif
			
	default init s0:
		function currentPlays = 0
		function userWins = 0
		function cpuWins = 0