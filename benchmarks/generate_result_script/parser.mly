%{
open Lexing
open Res
%}

%token Semicolon Dot Percent
%token File_end
%token <string>Id 
%token <int>Int 


%start input
%type <Res.res list>input

%%
input: inputs File_end	{$1}
;

inputs:	{[]}
	| ut st cpup ct asts auds ass ats mrss arss mpf mipf vcs ics swaps fsi fso sms smr sd ps es inputs	
		{
			{
				usr_time = $1; 
				sys_time = $2; 
				cpu_percent = $3; 
				clock_time = $4;
				avrg_sh_txt_size = $5;
				avrg_unsh_data_size = $6;
				avrg_stack_size = $7;
				avrg_total_size = $8;
				max_res_size = $9;
				avrg_res_size = $10;
				major_page_faults = $11;
				minor_page_faults = $12;
				vol_contxt_switch = $13;
				invol_contxt_switch = $14;
				swaps = $15;
				file_inputs = $16;
				file_outputs = $17;
				sock_msg_sent = $18;
				sock_msg_recv = $19;
				signal_deliver = $20;
				page_size = $21;
				exit_status = $22;
			} :: $23}
;

ut: Int Dot Int	{float_of_int($1) +. ((float_of_int $3) /. 100.0)};
st: Int Dot Int {float_of_int($1) +. ((float_of_int $3) /. 100.0)};
cpup: Int Percent	{$1};
ct: Int Semicolon Int Dot Int	{float_of_int ($1 * 60 + $3) +. ((float_of_int $5) /. 100.0)}
	| Int Semicolon Int Semicolon Int Dot Int	{float_of_int ($1 * 3600 + $3 * 60 + $5) +. ((float_of_int $7) /. 100.0)}
;
asts : Int	{$1};
auds : Int	{$1};
ass : Int	{$1};
ats : Int	{$1};
mrss : Int	{$1};
arss : Int	{$1};
mpf : Int	{$1};
mipf : Int	{$1};
vcs : Int	{$1};
ics : Int	{$1};
swaps : Int	{$1};
fsi : Int	{$1};
fso : Int	{$1};
sms : Int	{$1};
smr : Int	{$1};
sd : Int	{$1};
ps : Int	{$1};
es : Int	{$1};

/*
inputs: 
//	| FATAL_ERROR I M I DOT I S {[-1.0]}
//	| I M I DOT I S	{if !error_state then (error_state := false; [1200.1]) else [((float_of_int ($1 * 60 + $3)) +. ((float_of_int $5) /. 1000.0))]}
//	| FATAL_ERROR inputs	{error_state := true; print_endline "ecountered fatal error"; $2}
//	| FATAL_ERROR I M I DOT I S inputs {(-1.0) :: $8}
//	| I M I DOT I S inputs {if !error_state then (error_state := false; ((float_of_int ($1 * 60 + $3)) +. ((float_of_int $5) /. 1000.0)) :: ((1200.1) :: (List.tl $7))) else ((float_of_int ($1 * 60 + $3)) +. ((float_of_int $5) /. 1000.0)) :: $7}
	| FATAL_ERROR I	I {[$2]}
	| FATAL_ERROR I I inputs	{(-1) :: $4}
	| I	I {if $2 = 0 then [$1] else [$1]}
	| I I inputs	{if $2 = 0 then $1 :: $3 else ($1) :: $3}

; 

//single_input: 
//	| FATAL_ERROR I M I DOT I S {-1.0}
//	| I M I DOT I S	{((float_of_int ($1 * 60 + $3)) +. ((float_of_int $5) /. 1000.0))}
//	;
*/

%%

