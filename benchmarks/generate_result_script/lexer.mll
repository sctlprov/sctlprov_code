{
	open Parser
	let line_num = ref 0
}

let integer = ['0'-'9']+
let id = ['a'-'z' 'A' - 'Z'] ['a'-'z' 'A' - 'Z' '0'-'9' '_']*


rule token = parse
	| "User time (seconds):"	{token lexbuf}
	| "System time (seconds):"	{token lexbuf}
	| "Percent of CPU this job got:"	{token lexbuf}
	| "Elapsed (wall clock) time (h:mm:ss or m:ss):"	{token lexbuf}
	| "Average shared text size (kbytes):"	{token lexbuf}
	| "Average unshared data size (kbytes):"	{token lexbuf}
	| "Average stack size (kbytes):"	{token lexbuf}
	| "Average total size (kbytes):"	{token lexbuf}
	| "Maximum resident set size (kbytes):"	{token lexbuf}
	| "Average resident set size (kbytes):"	{token lexbuf}
	| "Major (requiring I/O) page faults:"	{token lexbuf}
	| "Minor (reclaiming a frame) page faults:"	{token lexbuf}
	| "Voluntary context switches:"	{token lexbuf}
	| "Involuntary context switches:"	{token lexbuf}
	| "Swaps:"	{token lexbuf}
	| "File system inputs:"	{token lexbuf}
	| "File system outputs:"	{token lexbuf}
	| "Socket messages sent:"	{token lexbuf}
	| "Socket messages received:"	{token lexbuf}
	| "Signals delivered:"	{token lexbuf}
	| "Page size (bytes):"	{token lexbuf}
	| "Exit status:"	{token lexbuf}
	| integer as i 	{Int (int_of_string i)}
	| "."	{Dot}
	| ":"	{Semicolon}
	| "%"	{Percent}
	| '\n'	{token lexbuf}
	| [' ' '\t' '\r']	{token lexbuf}
	| eof	{File_end}
	| _		{dummy lexbuf}
and dummy = parse
	| "User time (seconds):"	{token lexbuf}
	| '\n'	{dummy lexbuf}
	| [' ' '\t' '\r']	{dummy lexbuf}
	| eof	{dummy lexbuf}
	| _ 	{dummy lexbuf}

(**
rule token = parse
	| "exception encountered"	{FATAL_ERROR}
	| "Terminated"	{FATAL_ERROR}
	| "terminated by a signal" {FATAL_ERROR}
	| "Fatal error:"	{FATAL_ERROR}
	| "Maximum resident set size (kbytes):"	{token lexbuf}
	| "Exit status:"	{token lexbuf}
	| "real"	{token lexbuf}
	| "m" 		{M}
	| "s"		{S}
	| "."		{DOT}
	| integer as s	{I (int_of_string s)}
	| '\n'		{line_num := (!line_num) + 1; dummy lexbuf}
	| [' ' '\t' '\r']	{token lexbuf}
	| eof		{File_end}
	| _		{dummy lexbuf}
and dummy = parse
	| "exception encountered"	{FATAL_ERROR}
	| "Terminated"	{FATAL_ERROR}
	| "terminated by a signal" {FATAL_ERROR}
	| "Fatal error:"	{FATAL_ERROR}
	| "Maximum resident set size (kbytes):"	{token lexbuf}
	| "Exit status:"	{token lexbuf}
	| "real"	{token lexbuf}
	| '\n'		{line_num := (!line_num) + 1; dummy lexbuf}
	| [' ' '\t' '\r'] {dummy lexbuf}
	| eof		{File_end}
	| _		{dummy lexbuf}

**)
