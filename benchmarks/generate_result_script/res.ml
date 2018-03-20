type res = 
{
	usr_time : float;
	sys_time : float;
	cpu_percent : int;
	clock_time : float;
	avrg_sh_txt_size : int;
	avrg_unsh_data_size : int;
	avrg_stack_size : int;
	avrg_total_size : int;
	max_res_size : int;
	avrg_res_size : int;
	major_page_faults : int;
	minor_page_faults : int;
	vol_contxt_switch : int;
	invol_contxt_switch : int;
	swaps: int;
	file_inputs : int;
	file_outputs : int;
	sock_msg_sent : int;
	sock_msg_recv : int;
	signal_deliver : int;
	page_size : int;
	exit_status : int;
}