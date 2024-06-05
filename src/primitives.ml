let forbidden_operator = ["read" ; "write" ; "invoke"; "recv"; "send"; "open"; "close"; "close_conn"; "connect"; "accept"]

let primitive_ins = [("read", Syntax.IRead, [Etype.EtyVal]) ;
                     ("write", Syntax.IWrite, [Etype.EtyVal; Etype.EtyVal]) ; 
                     ("invoke", Syntax.IInvoke, 
                                 [Etype.EtyCh([Input.CRecv ; Input.CSend], [Input.CStream]); Etype.EtyVal; Etype.EtyVal]) ; 
                     ("recv", Syntax.IRecv, [Etype.EtyCh([Input.CRecv], [])]) ; 
                     ("send", Syntax.ISend, [Etype.EtyCh([Input.CSend], []); Etype.EtyVal]) ; 
                     ("open", Syntax.IOpen, [Etype.EtyVal]) ; 
                     ("close", Syntax.IClose, [Etype.EtyVal]) ; 
                     ("close_conn", Syntax.ICloseConn, [Etype.EtyCh([], [Input.CStream])]) ; 
                     ("connect", Syntax.IConnect, [Etype.EtyCh([], [Input.CStream])]) ; 
                     ("accept", Syntax.IAccept, [Etype.EtyCh([Input.CSend], [Input.CStream])])]

let check_primitive_ins i =
   List.exists (fun (n, _, _) -> n = i) primitive_ins

let is_forbidden_operator o = List.exists (fun s -> s = o) forbidden_operator 

