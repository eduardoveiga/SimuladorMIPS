#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#define N 256
#define linha1 8
#define linha2 4
char ARQ[30];
typedef struct instrucao {
	int op,funct,tipo,rs1,rt1,rd1,sh1,imediato,off,end1,extensao;
	char rs[6],rt[6],rd[6],end[11],offset[11],sh[6],im[11];
	int validade;
}Instrucao;
Instrucao memoria[N];
int data_memory[N];
int reg[32];
int pc,extensao,OrigPc,endereco,branched,JReg,sinalmux2,tag;
int dado_w,permissao_w,stall;
typedef struct sinais {
	int origpc,escrevereg,branch,regdst,origalu0,origalu1,lemem,escrevemem,memparareg,opalu,inversor,link;
}Sinais;
typedef struct forward {
    int A;
    int B;
}Forward;
Forward F_EX,F_MEM;
typedef struct if_id {
	Instrucao inst;
	int endereco;
	int exit;
}IF_ID;
typedef struct id_ex {
	int dado1,dado2,offset,rs,rt,rd,funct,shamt;
	int RegDst,EscreveReg,OrigALU1,OrigALU2,OrigPC,LeMem,EscreveMem,MemparaReg,OpAlu,Branch,Inversor,Link,deslocamento;
	Sinais sc;
	int exit;
	Instrucao inst;
}ID_EX;
typedef struct ex_mem {
	int EscreveReg,LeMem,EscreveMem,MemparaReg;
	int resultado,destino,dado_w,dado_wm,rd,rs,rt;
	int exit;
	Instrucao inst;
}EX_MEM;
typedef struct mem_wb {
	int EscreveReg,MemparaReg;
	int dado_r,resultado,destino,rd,rs,rt;
	int exit;
	Instrucao inst;
}MEM_WB;
typedef struct cacheinstrucoes {
	Instrucao inst;
	int m,r,v,tag;
}CacheInstrucoes;
CacheInstrucoes cacheinst[linha1][2];
typedef struct cachedados {
	int m,r,v,tag,dado;
}CacheDados;
CacheDados cachedado[linha1][2];
typedef struct cacheinstrucoes4 {
	Instrucao inst;
	int m,cont,v,tag;
}CacheInstrucoes4;
CacheInstrucoes4 cacheinst4[linha2][4];
typedef struct cachedados4 {
	int m,cont,v,tag,dado;
}CacheDados4;
CacheDados4 cachedado4[linha2][4];
int mux2 (int select,int a,int b) {
	if (select==0) {
		return a;
	}
	else {
		if (select==1) {
			return b;
		}
	}
}
int mux3 (int select,int a,int b,int c) {
	if (select==0) {
		return a;
	}
	else {
		if (select==1) {
			return b;
		}
		else {
			if (select==2) {
				return c;
			}
		}
	}
}
int mux4 (int select,int a,int b,int c,int d) {
	if (select==0) {
		return a;
	}
	else {
		if (select==1) {
			return b;
		}
		else {
			if (select==2) {
				return c;
			}
			else {
				if (select==3) {
					return d;
				}
			}
		}
	}
}
int mux5 (int select,int a,int b,int c,int d,int e) {
	if (select==0) {
		return a;
	}
	else {
		if (select==1) {
			return b;
		}
		else {
			if (select==2) {
				return c;
			}
			else {
				if(select==3) {
					return d;
				}
				else {
					if (select==4) {
						return e;
					}
				}
			}
		}
	}
}
int mux6 (int select,int a,int b,int c,int d,int e,int f) {
	if (select==0) {
		return a;
	}
	else {
		if (select==1) {
			return b;
		}
		else {
			if (select==2) {
				return c;
			}
			else {
				if (select==3) {
					return d;
				}
				else {
					if (select==4) {
						return e;
					}
					else {
						if (select==5) {
							return f;
						}
					}
				}
			}
		}
	}
}
void Hazard (IF_ID * fetch,ID_EX * decode,EX_MEM * execute,MEM_WB * memory) {
	if (memory->exit==1 || execute->exit==1 || decode->exit==1) {
	}
	else {
		if (memory->EscreveReg==1 && memory->destino!=0 && execute->rd!=decode->rs && memory->destino==decode->rs) {
			F_MEM.A=1;
		}
		else {
			F_MEM.A=0;
		}
		if (memory->EscreveReg==1 && memory->destino!=0 && execute->rd==decode->rs && memory->destino==decode->rs) {
			F_MEM.A=1;
			F_EX.A=2;
		}
		else {
			F_MEM.A=0;
			F_EX.A=0;
		}
		if (memory->EscreveReg==1 && memory->destino!=0 && execute->rd==decode->rt && memory->destino==decode->rs) {
			F_MEM.A=1;
			F_EX.B=2;
		}
		else {
			F_MEM.A=0;
			F_EX.B=0;
		}
		if (memory->EscreveReg==1 && memory->destino!=0 && execute->rd!=decode->rt && memory->destino==decode->rt) {
			F_MEM.B=1;
		}
		else {
			F_MEM.B=0;
		}
		if (memory->EscreveReg==1 && memory->destino!=0 && execute->rd==decode->rs && memory->destino==decode->rt) {
			F_MEM.B=1;
			F_EX.A=2;
		}
		else {
			F_MEM.B=0;
			F_EX.A=0;
		}
		if (memory->EscreveReg==1 && memory->destino!=0 && execute->rd==decode->rt && memory->destino==decode->rt) {
			F_MEM.B=1;
			F_EX.B=2;
		}
		else {
			F_MEM.B=0;
			F_EX.B=0;
		}
	}
	if (execute->exit==1 || decode->exit==1) {
	}
	else {
		if (decode->inst.op==0 && execute->inst.op==0) {
			if (execute->EscreveReg==1 && execute->rd!=0 && execute->rd==decode->rs) {
				F_EX.A=2;
			}
			else {
				F_EX.A=0;
			}
			if (execute->EscreveReg==1 && execute->rd!=0 && execute->rd==decode->rt) {
				F_EX.B=2;
			}
			else {
				F_EX.B=0;
			}
		}
		else {
			if (decode->inst.op!=0 && execute->inst.op!=0) {
				if (execute->EscreveReg==1 && execute->rt!=0 && execute->rt==decode->rs) {
					F_EX.A=2;
				}
				else {
					F_EX.A=0;
				}
			}
			else {
				if (execute->inst.op!=0 && decode->inst.op==0) {
					if (execute->EscreveReg==1 && execute->rt!=0 && execute->rt==decode->rs) {
						F_EX.A=2;
					}
					else {
						F_EX.A=0;
					}
					if (execute->EscreveReg==1 && execute->rt!=0 && execute->rt==decode->rt) {
						F_EX.B=2;
					}
					else {
						F_EX.B=0;
					}
				}
				else {
					if (execute->inst.op==0 && decode->inst.op!=0) {
						if (execute->EscreveReg==1 && execute->rd!=0 && execute->rd==decode->rs) {
							F_EX.A=2;
						}
						else {
							F_EX.A=0;
						}
					}
				}
			}
		}
	}
	if (memory->exit==1 || decode->exit==1) {
	}
	else {
		if (decode->inst.op==0 && memory->inst.op==0) {
			if (memory->EscreveReg==1 && memory->rd!=0 && memory->rd==decode->rs) {
				F_MEM.A=1;
			}
			else {
				F_MEM.A=0;
			}
			if (memory->EscreveReg==1 && memory->rd!=0 && memory->rd==decode->rt) {
				F_MEM.B=1;
			}
			else {
				F_MEM.B=0;
			}
		}
		else {
			if (decode->inst.op!=0 && memory->inst.op!=0) {
				if (memory->EscreveReg==1 && memory->rt!=0 && memory->rt==decode->rs) {
					F_MEM.A=1;
				}
				else {
					F_MEM.A=0;
				}
			}
			else {
				if (memory->inst.op!=0 && decode->inst.op==0) {
					if (memory->EscreveReg==1 && memory->rt!=0 && memory->rt==decode->rs) {
						F_MEM.A=1;
					}
					else {
						F_MEM.A=0;
					}
					if (memory->EscreveReg==1 && memory->rt!=0 && memory->rt==decode->rt) {
						F_MEM.B=1;
					}
					else {
						F_MEM.B=0;
					}
				}
				else {
					if (memory->inst.op==0 && decode->inst.op!=0) {
						if (memory->EscreveReg==1 && memory->rd!=0 && memory->rd==decode->rs) {
							F_MEM.A=1;
						}
						else {
							F_MEM.A=0;
						}
					}
				}
			}
		}
	}
	if (execute->exit==1 || decode->exit==1) {
	}
	else {
		if (decode->inst.op!=0 && execute->inst.op!=0) {
			if (decode->EscreveMem==1 && execute->rt!=0 && execute->rt==decode->rt) {
				F_MEM.B=3;
			}
			else {
				F_EX.B=0;
			}
		}
		if (decode->inst.op!=0 && execute->inst.op==0) {
			if (decode->EscreveMem==1 && execute->rd!=0 && execute->rd==decode->rt) {
				F_MEM.B=3;
			}
			else {
				F_MEM.B=0;
			}
		}
	}
}
void forward_control (ID_EX * decode, int opcao) {
	switch(opcao){
		case 1:
			break;
		case 2:
			switch (F_EX.A) {
				case 0:
					break;
				case 2:
					decode->OrigALU1=1;
					break;
			}
			switch (F_EX.B) {
				case 0:
					break;
				case 2:
					decode->OrigALU2=2;
					break;
			}
			switch (F_MEM.A) {
				case 0:
					break;
				case 1:
					decode->OrigALU1=3;
					break;
				case 3:
					sinalmux2=1;
					break;
			}
			switch (F_MEM.B) {
				case 0:
					break;
				case 1:
					decode->OrigALU2=5;
					break;
				case 3:
					sinalmux2=1;
					break;
			}
		}
	}
void inicializa_pipeline (IF_ID * fetch,ID_EX * decode,EX_MEM * execute,MEM_WB * memory) {
	fetch->inst.op=-1;
	fetch->inst.funct=0;
	fetch->inst.rd1=0;
	fetch->inst.rt1=0;
	fetch->inst.rs1=0;
	fetch->endereco=0;
	fetch->exit=0;
	decode->inst.op=-1;
	decode->inst.funct=0;
	decode->inst.rd1=0;
	decode->inst.rt1=0;
	decode->inst.rs1=0;
	decode->dado1=0;
	decode->dado2=0;
	decode->offset=0;
	decode->rs=0;
	decode->rt=0;
	decode->rd=0;
	decode->funct=0;
	decode->shamt=0;
	decode->RegDst=0;
	decode->EscreveReg=0;
	decode->OrigALU1=0;
	decode->OrigALU2=0;
	decode->OrigPC=0;
	decode->LeMem=0;
	decode->EscreveMem=0;
	decode->MemparaReg=0;
	decode->OpAlu=0;
	decode->deslocamento=0;
	decode->exit=0;
	execute->inst.op=-1;
	execute->inst.funct=0;
	execute->inst.rd1=0;
	execute->inst.rt1=0;
	execute->inst.rs1=0;
	execute->EscreveReg=0;
	execute->LeMem=0;
	execute->EscreveMem=0;
	execute->MemparaReg=0;
	execute->resultado=0;
	execute->destino=0;
	execute->dado_w=0;
	execute->dado_wm=0;
	execute->rd=0;
	execute->rs=0;
	execute->rt=0;
	execute->exit=0;
	memory->inst.op=-1;
	memory->inst.funct=0;
	memory->inst.rd1=0;
	memory->inst.rt1=0;
	memory->inst.rs1=0;
	memory->EscreveReg=0;
	memory->MemparaReg=0;
	memory->dado_r=0;
	memory->resultado=0;
	memory->destino=0;
	memory->rd=0;
	memory->rs=0;
	memory->rd=0;
	memory->exit=0;
}
void flush (ID_EX * decode) {
	decode->dado1=0;
	decode->dado2=0;
	decode->offset=0;
	decode->rs=0;
	decode->rt=0;
	decode->rd=0;
	decode->funct=0;
	decode->shamt=0;
	decode->RegDst=0;
	decode->EscreveReg=0;
	decode->OrigALU1=0;
	decode->OrigALU2=0;
	decode->OrigPC=0;
	decode->LeMem=0;
	decode->EscreveMem=0;
	decode->MemparaReg=0;
	decode->OpAlu=0;
	decode->deslocamento=0;
	decode->exit=0;
}
void inicializa_ram () {
	int i;
	for (i=0;i<N;i++) {
		memoria[i].validade=0;
	}
}
void inicializa_mdados () {
	int i;
	for (i=0;i<N;i++) {
		data_memory[i]=0;
	}
}
int char2int (char c) {
	int x;
	if (c=='0') {
		x=0;
	}
	else {
		if (c=='1') {
			x=1;
		}
		else {
			if (c=='2') {
				x=2;
			}
			else {
				if (c=='3') {
					x=3;
				}
				else {
					if (c=='4') {
						x=4;
					}
					else {
						if (c=='5') {
							x=5;
						}
						else {
							if (c=='6') {
								x=6;
							}
							else {
								if (c=='7') {
									x=7;
								}
								else {
									if (c=='8') {
										x=8;
									}
									else {
										if (c=='9') {
											x=9;
										}
									}
								}
							}
						}
					}
				}
			}
		}
	}
	return x;
}
int inteiro (char * vet,int cont) {
	int y,e,i,j,x;
	y=0;
	i=cont-1;
	if (vet[0]=='-') {
		while (i>0) {
			for (j=0;j<cont-1;j++) {
				e=(int)pow(10,j);
				x=char2int(vet[i]);
				y=(x*e)+y;
				i--;
			}
		}
		return -y;
	}
	else {
		while (i>=0) {
			for (j=0;j<cont;j++) {
				e=(int)pow(10,j);
				x=char2int(vet[i]);
				y=(x*e)+y;
				i--;
			}
		}
		return y;
	}
}
int busca_linha (char * arquivo, char * chave) {
	int retorno;
    FILE *File;
    File=fopen(arquivo,"r");
    char *linha=(char*)malloc(65536);
    int i;
    for (i=0;i<65536;i+=1) {
		linha[i]=0;
    }
    int linha_num=0;
    int acordo=0;
    char palavra=5;
    while (1) {
		acordo=0;
        palavra=fgetc(File);
        while (1) {
			if (feof(File) || palavra=='\n' || acordo>32768) {
				linha_num+=1;
                linha[acordo]=0;
                if (strstr(linha,chave)) {
					retorno=linha_num;
                }
                break;
            }
            else {
				linha[acordo]=palavra;
                palavra=fgetc(File);
                acordo++;
            }
        }
        if (feof(File)) {
			return retorno-1;
            break;
        }
    }
}
Sinais inicializa_sinal (Sinais sc) {
	sc.link=0;
	sc.origpc=0;
	sc.escrevereg=0;
	sc.branch=0;
	sc.regdst=0;
	sc.origalu0=0;
	sc.origalu1=0;
	sc.lemem=0;
	sc.escrevemem=0;
	sc.memparareg=0;
	sc.opalu=0;
	sc.inversor=0;
	return sc;
}
int valor_registrador (char * nome) {
    int x;
	if ((strcmp(nome,"$zero")==0)||(strcmp(nome,"0")==0)) {
			x=0;
	}
	else {
		if ((strcmp(nome,"$at")==0)||(strcmp(nome,"1")==0)) {
			x=1;
		}
		else {
			if ((strcmp(nome,"$v0")==0)||(strcmp(nome,"2")==0)) {
				x=2;
			}
			else {
				if ((strcmp(nome,"$v1")==0)||(strcmp(nome,"3")==0)) {
					x=3;
				}
				else {
					if ((strcmp(nome,"$a0")==0)||(strcmp(nome,"4")==0)) {
						x=4;
					}
					else {
						if ((strcmp(nome,"$a1")==0)||(strcmp(nome,"5")==0)) {
							x=5;
						}
						else {
							if ((strcmp(nome,"$a2")==0)||(strcmp(nome,"6")==0)) {
								x=6;
							}
							else {
								if ((strcmp(nome,"$a3")==0)||(strcmp(nome,"7")==0)) {
									x=7;
								}
								else {
									if ((strcmp(nome,"$t0")==0)||(strcmp(nome,"8")==0)) {
										x=8;
									}
									else {
										if ((strcmp(nome,"$t1")==0)||(strcmp(nome,"9")==0)) {
											x=9;
										}
										else {
											if ((strcmp(nome,"$t2")==0)||(strcmp(nome,"10")==0)) {
												x=10;
											}
											else {
												if ((strcmp(nome,"$t3")==0)||(strcmp(nome,"11")==0)) {
													x=11;
												}
												else {
													if ((strcmp(nome,"$t4")==0)||(strcmp(nome,"12")==0)) {
														x=12;
													}
													else {
														if ((strcmp(nome,"$t5")==0)||(strcmp(nome,"13")==0)) {
															x=13;
														}
														else {
															if ((strcmp(nome,"$t6")==0)||(strcmp(nome,"14")==0)) {
																x=14;
															}
															else {
																if ((strcmp(nome,"$t7")==0)||(strcmp(nome,"15")==0)) {
																	x=15;
																}
															}
														}
													}
												}
											}
										}
									}
								}
							}
						}
					}
				}
			}
		}
	}
	if ((strcmp(nome,"$s0")==0)||(strcmp(nome,"16")==0)) {
		x=16;
	}
	else {
		if ((strcmp(nome,"$s1")==0)||(strcmp(nome,"17")==0)) {
			x=17;
		}
		else {
			if ((strcmp(nome,"$s2")==0)||(strcmp(nome,"18")==0)) {
				x=18;
			}
			else {
				if ((strcmp(nome,"$s3")==0)||(strcmp(nome,"19")==0)) {
					x=19;
				}
				else {
					if ((strcmp(nome,"$s4")==0)||(strcmp(nome,"20")==0)) {
						x=20;
					}
					else {
						if ((strcmp(nome,"$s5")==0)||(strcmp(nome,"21")==0)) {
							x=21;
						}
						else {
							if ((strcmp(nome,"$s6")==0)||(strcmp(nome,"22")==0)) {
								x=22;
							}
							else {
								if ((strcmp(nome,"$s7")==0)||(strcmp(nome,"23")==0)) {
									x=23;
								}
								else {
									if ((strcmp(nome,"$t8")==0)||(strcmp(nome,"24")==0)) {
										x=24;
									}
									else {
										if ((strcmp(nome,"$t9")==0)||(strcmp(nome,"25")==0)) {
											x=25;
										}
										else {
											if ((strcmp(nome,"$k0")==0)||(strcmp(nome,"26")==0)) {
												x=26;
											}
											else {
												if ((strcmp(nome,"$k1")==0)||(strcmp(nome,"27")==0)) {
													x=27;
												}
												else {
													if ((strcmp(nome,"$gp")==0)||(strcmp(nome,"28")==0)) {
														x=28;
													}
													else {
														if ((strcmp(nome,"$sp")==0)||(strcmp(nome,"29")==0)) {
															x=29;
														}
														else {
															if ((strcmp(nome,"$fp")==0)||(strcmp(nome,"30")==0)) {
																x=30;
															}
															else {
																if ((strcmp(nome,"$ra")==0)||(strcmp(nome,"31")==0)) {
																	x=31;
																}
															}
														}
													}
												}
											}
										}
									}
								}
							}
						}
					}
				}
			}
		}
	}
    return(x);
}
void filtro (char * inst,Instrucao x,int n,FILE * disco) {
	int i,j,aux,aux1,aux2;
	char nome[5];
	for (i=0;inst[i]!=' ';i++) {
		nome[i]=inst[i];
		aux=i;
	}
	nome[aux+1]='\0';
	if ((strcmp(nome,"add")==0)||(strcmp(nome,"sub")==0)||(strcmp(nome,"and")==0)||(strcmp(nome,"nor")==0)||(strcmp(nome,"or")==0)||(strcmp(nome,"slt")==0)||(strcmp(nome,"mul")==0))  {
		x.tipo=00;
		x.op=0;
		x.sh1=0;
		x.end1=0;
		x.off=0;
		x.imediato=0;
		j=0;
		for (i=aux+2;inst[i]!=',';i++) {
			x.rd[j]=inst[i];
			j++;
			aux1=i;
		}
		x.rd[j]='\0';
		x.rd1=valor_registrador(x.rd);
		j=0;
		for (i=aux1+2;inst[i]!=',';i++) {
			x.rs[j]=inst[i];
			j++;
			aux2=i;
		}
		x.rs[j]='\0';
		x.rs1=valor_registrador(x.rs);
		j=0;
		for (i=aux2+2;inst[i]!=';';i++) {
			x.rt[j]=inst[i];
			j++;
		}
		x.rt[j]='\0';
		x.rt1=valor_registrador(x.rt);
		if (strcmp(nome,"add")==0) {
            x.funct=32;
		}
		else {
			if (strcmp(nome,"sub")==0) {
				x.funct=34;
			}
			else {
				if (strcmp(nome,"and")==0) {
					x.funct=36;
				}
				else {
					if (strcmp(nome,"nor")==0) {
						x.funct=39;
				    }
					else {
						if (strcmp(nome,"or")==0) {
							x.funct=37;
						}
						else {
							if (strcmp(nome,"slt")==0) {
								x.funct=42;
								}
							else {
								if(strcmp(nome,"mul")==0) {
									x.funct=90;
								}
							}

						}
					}
				}
			}
		}
	}
	if (strcmp(nome,"jr")==0) {
		x.tipo=01;
		x.op=0;
		x.sh1=0;
		x.funct=8;
		x.rd1=0;
		x.rt1=0;
		x.imediato=0;
		x.off=0;
		x.end1=0;
		j=0;
		for (i=aux+2;inst[i]!=';';i++) {
			x.rs[j]=inst[i];
			j++;
		}
		x.rs[j]='\0';
		x.rs1=valor_registrador(x.rs);
	}
	if ((strcmp(nome,"sll")==0)||(strcmp(nome,"srl")==0)) {
		x.tipo=02;
		x.op=0;
		x.rt1=0;
		x.imediato=0;
		x.off=0;
		x.end1=0;
		j=0;
		for (i=aux+2;inst[i]!=',';i++) {
			x.rd[j]=inst[i];
			j++;
			aux1=i;
		}
		x.rd[j]='\0';
		x.rd1=valor_registrador(x.rd);
		j=0;
		for (i=aux1+2;inst[i]!=',';i++) {
			x.rs[j]=inst[i];
			j++;
			aux2=i;
		}
		x.rs[j]='\0';
		x.rs1=valor_registrador(x.rs);
		j=0;
		for (i=aux2+2;inst[i]!=';';i++) {
			x.sh[j]=inst[i];
			j++;
		}
		x.sh[j]='\0';
		x.sh1=inteiro(x.sh,j);
		if (strcmp(nome,"sll")==0) {
			x.funct=0;
        }
		else {
			if (strcmp(nome,"srl")==0) {
				x.funct=2;
			}
		}
	}
	if ((strcmp(nome,"addi")==0)||(strcmp(nome,"ori")==0)||(strcmp(nome,"slti")==0)) {
		x.tipo=10;
		x.funct=0;
		x.rd1=0;
		x.sh1=0;
		x.off=0;
		x.end1=0;
		if (strcmp(nome,"addi")==0) {
            x.op=8;
		}
		else {
			if (strcmp(nome,"ori")==0) {
				x.op=13;
			}
			else {
				if (strcmp(nome,"slti")==0) {
					x.op=10;
				}
			}
		}
		j=0;
		for (i=aux+2;inst[i]!=',';i++) {
			x.rt[j]=inst[i];
			j++;
			aux1=i;
		}
		x.rt[j]='\0';
		x.rt1=valor_registrador(x.rt);
		j=0;
		for (i=aux1+2;inst[i]!=',';i++) {
			x.rs[j]=inst[i];
			j++;
			aux2=i;
		}
		x.rs[j]='\0';
		x.rs1=valor_registrador(x.rs);
		j=0;
		for (i=aux2+2;inst[i]!=';';i++) {
			x.im[j]=inst[i];
			j++;
		}
		x.im[j]='\0';
		x.imediato=inteiro(x.im,j);
		x.off=x.imediato;

	}
	if ((strcmp(nome,"beq")==0)||(strcmp(nome,"bne")==0)) {
		x.tipo=10;
		x.funct=0;
		x.rd1=0;
		x.sh1=0;
		x.off=0;
		x.imediato=0;
		if (strcmp(nome,"beq")==0) {
			x.op=4;
		}
		else {
			if (strcmp(nome,"bne")==0) {
				x.op=5;
			}
		}
		j=0;
		for (i=aux+2;inst[i]!=',';i++) {
			x.rs[j]=inst[i];
			j++;
			aux1=i;
		}
		x.rs[j]='\0';
		x.rs1=valor_registrador(x.rs);
		j=0;
		for (i=aux1+2;inst[i]!=',';i++) {
			x.rt[j]=inst[i];
			j++;
			aux2=i;
		}
		x.rt[j]='\0';
		x.rt1=valor_registrador(x.rt);
		j=0;
		for (i=aux2+2;inst[i]!=';';i++) {
			x.end[j]=inst[i];
			j++;
		}
		x.end[j]='\0';
		if (x.end[0]=='-'||x.end[0]=='0'||x.end[0]=='1'||x.end[0]=='2'||x.end[0]=='3'||x.end[0]=='4'||x.end[0]=='5'||x.end[0]=='6'||x.end[0]=='7'||x.end[0]=='8'||x.end[0]=='9') {
			x.end1=inteiro(x.end,j);
		}
		else {
			strcat(x.end, ":");
			x.end1=busca_linha(ARQ,x.end);
		}
	}
	if (strcmp(nome,"lui")==0) {
		x.tipo=11;
		x.op=15;
		x.funct=0;
		x.rs1=0;
		x.rd1=0;
		x.sh1=0;
		x.off=0;
		x.end1=0;
		j=0;
		for (i=aux+2;inst[i]!=',';i++) {
			x.rt[j]=inst[i];
			j++;
			aux1=i;
		}
		x.rt[j]='\0';
		x.rt1=valor_registrador(x.rt);
		j=0;
		for (i=aux1+2;inst[i]!=';';i++) {
			x.im[j]=inst[i];
			j++;
		}
		x.im[j]='\0';
		x.imediato=inteiro(x.im,j);
		x.off=x.imediato;

	}
	if (strcmp(nome,"lw")==0) {
		x.tipo=12;
        x.op=35;
		x.funct=0;
		x.rd1=0;
		x.sh1=0;
		x.imediato=0;
		x.end1=0;
		j=0;
		for (i=aux+2;inst[i]!=',';i++) {
			x.rt[j]=inst[i];
			j++;
			aux1=i;
		}
		x.rt[j]='\0';
		x.rt1=valor_registrador(x.rt);
		j=0;
		for (i=aux1+2;inst[i]!='(';i++) {
			x.offset[j]=inst[i];
			j++;
			aux2=i;
		}
		x.offset[j]='\0';
		x.off=inteiro(x.offset,j);
		j=0;
		for (i=aux2+2;inst[i]!=')';i++) {
			x.rs[j]=inst[i];
			j++;
		}
		x.rs[j]='\0';
		x.rs1=valor_registrador(x.rs);
	}
	if (strcmp(nome,"sw")==0) {
		x.tipo=13;
		x.op=43;
		x.funct=0;
		x.rd1=0;
		x.sh1=0;
		x.imediato=0;
		x.end1=0;
		j=0;
		for (i=aux+2;inst[i]!=',';i++) {
			x.rt[j]=inst[i];
			j++;
			aux1=i;
		}
		x.rt[j]='\0';
		x.rt1=valor_registrador(x.rt);
		j=0;
		for (i=aux1+2;inst[i]!='(';i++) {
			x.offset[j]=inst[i];
			j++;
			aux2=i;
		}
		x.offset[j]='\0';
		x.off=inteiro(x.offset,j);
		j=0;
		for (i=aux2+2;inst[i]!=')';i++) {
			x.rs[j]=inst[i];
			j++;
		}
		x.rs[j]='\0';
		x.rs1=valor_registrador(x.rs);
	}
	if (strcmp(nome,"nop")==0) {
		x.rs1=0;
		x.rt1=0;
		x.rd1=0;
		x.sh1=0;
		x.funct=0;
		x.imediato=0;
		x.op=1;
	}
	if (strcmp(nome,"j")==0||strcmp(nome,"jal")==0) {
		x.tipo=2;
		x.rs1=0;
		x.rt1=0;
		x.rd1=0;
		x.sh1=0;
		x.funct=0;
		x.imediato=0;
		if (strcmp(nome,"j")==0) {
            x.op=2;
		}
		else {
			if (strcmp(nome,"jal")==0) {
				x.op=3;
			}
		}
		j=0;
		for (i=aux+2;inst[i]!=';';i++) {
			x.end[j]=inst[i];
			j++;
		}
		x.end[j]='\0';
		if (x.end[0]=='-'||x.end[0]=='0'||x.end[0]=='1'||x.end[0]=='2'||x.end[0]=='3'||x.end[0]=='4'||x.end[0]=='5'||x.end[0]=='6'||x.end[0]=='7'||x.end[0]=='8'||x.end[0]=='9') {
			x.end1=inteiro(x.end,j);
		}
		else {
			strcat(x.end, ":");
			x.end1=busca_linha(ARQ,x.end);
		}
	}
	x.validade=1;
	fwrite(&x,sizeof(Instrucao),1,disco);
}
void carrega_memoria (FILE * disco,int cont) {
	int i;
	fread(memoria,sizeof(Instrucao),cont,disco);
}
void imprime_mem (Instrucao memoria[],int cont) {
	int i;
	for (i=0;i<N;i++) {
		printf("\nop: %.2d\n", memoria[i].op);
		printf("rd: %.2d\n", memoria[i].rd1);
		printf("rs: %.2d\n", memoria[i].rs1);
		printf("rt: %.2d\n", memoria[i].rt1);
		printf("offset:%.2s\n", memoria[i].offset);
		printf("validade:%.2d\n",memoria[i].validade);
	}
}
void imprime_mem_dados (int memoria[]) {
	int i;
	for (i=0;i<N;i++) {
		printf("\nmemoria de dados [%.2d]: %.4d\n" , i, memoria[i]);
	}
}
void imprime_cache_dados(CacheDados cachedado[][2]){
	int i,j;
	for(i=0;i<linha1;i++){
		for(j=0;j<2;j++){
			printf("cache de dados [%.2d][%.2d] %.4d\n",i,j,cachedado[i][j].dado);
		}
	}


}
void inicializa (int *reg) {
	int i;
	for (i=0;i<32;i++) {
		reg[i]=0;
	}
	reg[29]=N-1;
}
void imprime (int *reg) {
	int i,j,cont=0;
	printf("\nRegistradores:\n");
	for (i=0;i<8;i++) {
		for (j=0;j<4;j++) {
			printf("R(%d)=%.4d\t\t",cont,reg[cont]);
			cont++;
		}
		printf("\n");
	}
}
int logaritmo (int conj) {
	int cont,r;
	cont=0;
	r=1;
	while (r<conj) {
		r=r*2;
		cont++;
	}
	return cont;
}
void instruction_fetch (IF_ID * fetch,ID_EX * decode,int op) {
	int i,cachemiss,j,k,endmem,endcache,x,bitsindice,tag,cont1,cont2,cont3,cont4;
	cachemiss=1;
	int menor=0;
	x=0;
	if (permissao_w==0) {
		permissao_w=1;
		stall=0;
	}
	else {
		switch (op) {
			case 1:
				//fetch->inst=memoria[pc];
				endcache=pc%(linha1);
				bitsindice=logaritmo(linha1);
				tag=pc>>bitsindice;
				while (cachemiss==1) {
					for (i=0;i<2;i++) {			//Buscar na cache
						if (cacheinst[endcache][i].v==1) {
							if (cacheinst[endcache][i].tag==tag) {
								fetch->inst=cacheinst[endcache][i].inst;
								cacheinst[endcache][i].r=1;
								if (i==0) {
									cacheinst[endcache][1].r=0;
								}
								else {
									cacheinst[endcache][0].r=0;
								}
								cachemiss=0;
								i=3;
							}
						}
					}
					if (cachemiss==1) {
						for (j=0;j<2;j++) {	//Buscar na memória
							if (cacheinst[endcache][j].v==0){
								cacheinst[endcache][j].inst=memoria[pc];
								cacheinst[endcache][j].v=1;
								cacheinst[endcache][j].r=1;
								cacheinst[endcache][j].tag=pc>>bitsindice;
								if (j==0) {
									cacheinst[endcache][1].r=0;
								}
								else {
									cacheinst[endcache][0].r=0;
								}
								j=3;
								x=1;
							}
							else x=0;
						}
						if (x==0) {
							//printf("x %d\n", x);
							for (j=0;j<2;j++) { //busca e substituição
								if(cacheinst[endcache][j].r==0) {
									if (cacheinst[endcache][j].m==1) {
										endmem=tag<<bitsindice;
										endmem=endmem & endcache;
										memoria[endmem]=cacheinst[endcache][j].inst;
										cacheinst[endcache][j].m=0;
									}
									cacheinst[endcache][j].inst=memoria[pc];
									cacheinst[endcache][j].tag=pc>>bitsindice;
									cacheinst[endcache][j].r=1;
									if (j==0) {
										cacheinst[endcache][1].r=0;
									}
									else {
										cacheinst[endcache][0].r=0;
									}
									j=3;
									x=0;
								}
							}
						}
					}
				}
				break;
			case 2:
				endcache=pc%(linha2);
				bitsindice=logaritmo(linha2);
				tag=pc>>bitsindice;
				while (cachemiss==1) {
					for (i=0;i<4;i++) {			//Buscar na cache
						if (cacheinst4[endcache][i].v==1) {
							if (cacheinst4[endcache][i].tag==tag) {
								fetch->inst=cacheinst4[endcache][i].inst;
								cacheinst4[endcache][i].cont++;
								/*if (i==0) {
									cacheinst4[endcache][1].r=0;
								}
								else {
									cacheinst[endcache][0].r=0;
								}*/
								cachemiss=0;
								i=4;
							}
						}
					}
					if (cachemiss==1) {
						for (j=0;j<4;j++) {	//Buscar na memória
							if (cacheinst4[endcache][j].v==0){
								cacheinst4[endcache][j].inst=memoria[pc];
								cacheinst4[endcache][j].v=1;
								//cacheinst4[endcache][j].r=1;
								cacheinst4[endcache][j].tag=pc>>bitsindice;
								cacheinst4[endcache][j].cont++;
								/*if (j==0) {
									cacheinst[endcache][1].r=0;
								}
								else {
									cacheinst[endcache][0].r=0;
								}			*/
								j=4;
								x=1;
							}
							else x=0;
						}
						if (x==0) {
							for (j=0;j<4;j++) { //busca e substituição
								if(cacheinst4[endcache][j].cont<menor){
									menor=cacheinst4[endcache][j].cont;
									}
								}
									if (cacheinst4[endcache][menor].m==1) {
										endmem=tag<<bitsindice;
										endmem=endmem & endcache;
										memoria[endmem]=cacheinst[endcache][menor].inst;
										cacheinst4[endcache][menor].m=0;
									}
									for(k=0;k<4;k++){
										cacheinst4[endcache][k].cont=0;
										}
									cacheinst4[endcache][menor].inst=memoria[pc];
									cacheinst4[endcache][menor].tag=pc>>bitsindice;
									cacheinst4[endcache][menor].cont++;
									//cacheinst4[endcache][j].r=1;
									/*if (j==0) {
										cacheinst[endcache][1].r=0;
									}
									else {
										cacheinst[endcache][0].r=0;
									}*/
									j=4;
									x=0;


						}
					}
				}
				break;
		}
		if (memoria[pc].validade==0) {
			fetch->exit=1;
		}
		else {
			pc=mux4(OrigPc,pc+1,extensao,endereco,JReg);
			fetch->endereco=pc;
			//printf("pc %d", pc);
		}
	}
}
Sinais controle (int op,int funct,Sinais * sc) {
	switch (op) {
		case 0:
			sc->regdst=1;
			sc->escrevereg=1;
			sc->opalu=2;
			if ((funct==0)||(funct==2)) {
				sc->origalu1=3;
			}
			if (funct==8) {
				sc->origpc=3;
			}
			break;
		case 1:
			sc->link=0;
			sc->origpc=0;
			sc->escrevereg=0;
			sc->branch=0;
			sc->regdst=0;
			sc->origalu0=0;
			sc->origalu1=0;
			sc->lemem=0;
			sc->escrevemem=0;
			sc->memparareg=0;
			sc->opalu=0;
			sc->inversor=0;
			break;
		case 2:
			sc->origpc=2;
			break;
		case 3:
			sc->origpc=2;
			sc->link=1;
			break;
		case 4:
			sc->opalu=1;
			sc->branch=1;
			break;
		case 5:
			sc->opalu=1;
			sc->branch=1;
			sc->inversor=1;
			break;
		case 8:
			sc->origalu1=1;
			sc->escrevereg=1;
			break;
		case 10:
			sc->opalu=3;
			sc->origalu1=1;
			sc->escrevereg=1;
			break;
		case 13:
			sc->origalu1=1;
			sc->opalu=4;
			sc->escrevereg=1;
			break;
		case 15:
			sc->opalu=5;
			sc->origalu0=2;
			sc->origalu1=4;
			sc->escrevereg=1;
			break;
		case 35:
			sc->origalu1=1;
			sc->lemem=1;
			sc->escrevereg=1;
			sc->memparareg=1;
			break;
		case 43:
            sc->origalu1=1;
			sc->escrevemem=1;
			break;
	}
	return *sc;
}
int extensao_sinal (Instrucao Inst,int extensao) {
	if ((Inst.tipo==00)||(Inst.tipo==01)||(Inst.tipo==02)) {
		extensao=((Inst.rd1*2048|Inst.sh1*64|Inst.funct));
	}
	else {
		if (Inst.tipo==10) {
			if ((Inst.op==8)||(Inst.op==13)||(Inst.op==10)) {
				extensao=Inst.imediato;
			}
			else {
				extensao=Inst.end1;
			}
		}
		else {
			if (Inst.tipo==11) {
				extensao=Inst.imediato;
			}
			else {
				if ((Inst.tipo==12)||(Inst.tipo==13)) {
					extensao=Inst.off;
				}
			}
		}
	}
	return extensao;
}

void printinst(Instrucao * Inst){
if (Inst->op==-1){
    //}Instrucao;


}
else {
    if(Inst->op==0){
        printf("opcode %.2d\n", Inst->op);
        printf("rs %.2d\n", Inst->rs1);
        printf("rt %.2d\n", Inst->rt1);
        printf("rd %.2d\n", Inst->rd1);
        printf("Shamt %.2d\n", Inst->sh1);
        printf("funct %.2d\n", Inst->funct);
    }
    else{
        if(Inst->op==2 || Inst->op==3){
            printf("opcode %.2d\n", Inst->op);
            printf("endereço %.6d", Inst->end1);
        }
        else{
            printf("opcode %.2d\n", Inst->op);
            printf("rs %.2d\n", Inst->rs1);
            printf("rt %.2d\n", Inst->rt1);
            printf("imediato %.2d\n", Inst->off);



        }
    }
}
}


void print (IF_ID * fetch,ID_EX * decode,EX_MEM* execute,MEM_WB * memory) {
	if (fetch->inst.validade==0) {
	}
	else {
		//printf("\n\t IF_ID\n\n");
		if (fetch->exit==1||fetch->inst.op==-1) {
			//printf("exit  %d", fetch->exit);
		}
		else {

			printf("PC %.2d\n",pc);
			printf("pc incrementado %.2d\n",fetch->endereco);
			printf("\n\t Fetch\n\n");
			printinst(&fetch->inst);
			//printf("executando Instruçao\n op %d \nrs %d \nrt %d \nrd %d \nsh %d\n",fetch->inst.op,fetch->inst.rs1,fetch->inst.rt1,fetch->inst.rd1,fetch->inst.sh1,fetch->inst.funct);
			//printf("imediato %d \nendereço %d \noffset %d\n\n\n\n",fetch->inst.imediato,fetch->inst.end1,fetch->inst.off);
		}

		if (decode->exit==1||decode->inst.op==-1) {
			//printf("exit Ativo? %d\n",decode->exit);
		}
		else {
		    printf("\n\tDecode\n\n");
			printinst(&decode->inst);
			//printf("executando Instruçao\n op %d \nrs %d \nrt %d \nrd %d \nsh %d\n",decode->inst.op,decode->inst.rs1,decode->inst.rt1,decode->inst.rd1,decode->inst.sh1,decode->inst.funct);
			//printf("imediato %d \nendereço %d \noffset %d\n\n\n\n",decode->inst.imediato,decode->inst.end1,decode->inst.off);
			printf("\n\tsinais de controle\n");
			printf("\tOrigPC %.2d\n",OrigPc);
			printf("\tEscreveReg %.2d\n",decode->EscreveReg);
			printf("\tBranch %.2d \n",decode->Branch);
			printf("\tRegDst %.2d\n",decode->RegDst);
			printf("\tOrigALU0 %.2d\n",decode->OrigALU1);
			printf("\tOrigALU1 %.2d\n",decode->OrigALU2);
			printf("\tLeMem %.2d \n",decode->LeMem);
			printf("\tEscreveMem %.2d\n",decode->EscreveMem);
			printf("\tMemParaReg %.2d\n",decode->MemparaReg);
			printf("\tOpAlU %.2d \n",decode->OpAlu);
			printf("\tInversor %.2d \n",decode->Inversor);
			printf("\tLink %.2d \n\n",decode->Link);
			printf("dado 1: %.2d\n dado 2: %.2d\n deslocamento %.2d\n",decode->dado1,decode->dado2,decode->deslocamento);
		}
		if (execute->exit==1||execute->inst.op==-1) {
		}
		else {
		    		printf("\n\tExecute\n\n");

			printinst(&execute->inst);

			//;;printf("executando Instruçao \nop %d \nrs %d \nrt %d \nrd %d \nsh %d\n",execute->inst.op,execute->inst.rs1,execute->inst.rt1,execute->inst.rd1,execute->inst.sh1,execute->inst.funct);
			//pintf("imediato %d \nendereço %d \noffset %d\n\n\n\n",execute->inst.imediato,execute->inst.end1,execute->inst.extensao);
			printf("\nEscreveReg %.2d",execute->EscreveReg);
			printf("\nLeMem %.2d",execute->LeMem);
			printf("\nMemparaReg %.2d",execute->MemparaReg);
			printf("\nresultado %.2d",execute->resultado);
			printf("\ndestino %.2d",execute->destino);
			printf("\ndado_w %.2d",execute->dado_w);
			printf("\ndado_wm %.2d",execute->dado_wm);
			printf("\nrd %.2d",execute->rd);
			printf("\nrs %.2d",execute->rs);
			printf("\nrt %2d",execute->rt);
		}

		if (memory->exit==1 ||memory->inst.op==-1) {
			//printf("exit Ativo? %d",memory->exit);
		}
		else {
		    printf("\n\tMemory\n\n");
			printinst(&memory->inst);

			//printf("executando Instruçao \nop %d \nrs %d \nrt %d \nrd %d \nsh %d\n",memory->inst.op,memory->inst.rs1,memory->inst.rt1,memory->inst.rd1,memory->inst.sh1,memory->inst.funct);
			//printf("imediato %d \nendereço %d \noffset %d\n\n\n\n",memory->inst.imediato,memory->inst.end1,memory->inst.extensao);

			printf("\nEscreveReg %.2d",memory->EscreveReg);
			printf("\nMemparaReg %.2d",memory->MemparaReg);
			printf("\ndado_r %.2d",memory->dado_r);
			printf("\nreultado %.2d",memory->resultado);
			printf("\ndestino %.2d",memory->destino);
			printf("\nrd %.2d",memory->rd);
			printf("\nrs %.2d",memory->rs);
			printf("\nrt %.2d",memory->rt);

			printf("\n\tWriteback\n");
			printinst(&memory->inst);

			printf("\n\nMemparareg %.2d\n",memory->MemparaReg);
			printf("Destino %.2d\n",memory->destino);
			printf("Escrevereg %.2d\n",memory->EscreveReg);
			printf("dado W %.2d\n",dado_w);






		}
	}
}

void instruction_decode (IF_ID * fetch,ID_EX * decode,int * Reg,Sinais * sc) {
	int z;
	if (permissao_w==0) {
	}
	else {
		decode->exit=fetch->exit;
		if (decode->exit==1) {
		}
		else {
			if (branched==1) {
				flush(decode);
				branched=0;
			}
			else {
				decode->inst=fetch->inst;
				*sc=inicializa_sinal(*sc);
				if (fetch->inst.op!=-1) {
					*sc=controle(fetch->inst.op,fetch->inst.funct,sc);
				}
				else {
				}
				decode->RegDst=sc->regdst;
				decode->EscreveReg=sc->escrevereg;
				decode->OrigALU1=sc->origalu0;
				decode->OrigALU2=sc->origalu1;
				decode->OrigPC=sc->origpc;
				decode->Branch=sc->branch;
				decode->Inversor=sc->inversor;
				decode->Link=sc->link;
				decode->LeMem=sc->lemem;
				decode->EscreveMem=sc->escrevemem;
				decode->MemparaReg=sc->memparareg;
				decode->OpAlu=sc->opalu;
				decode->funct=fetch->inst.funct;
				decode->dado1=reg[fetch->inst.rs1];
				JReg=reg[fetch->inst.rs1];
				//printf("JGEG %d", JReg);
				decode->dado2=reg[fetch->inst.rt1];
				decode->rs=fetch->inst.rs1;
				decode->rt=fetch->inst.rt1;
				decode->rd=fetch->inst.rd1;
				decode->shamt=fetch->inst.sh1;
				extensao=extensao_sinal(fetch->inst,fetch->inst.extensao);
				//printf("\nExtensão: %d \n",extensao);
				//printf("\nDado 2: %d \n",decode->dado2);
				endereco=fetch->inst.end1;
				decode->deslocamento=extensao<<16;
				fetch->inst.extensao=((extensao)*4)+(fetch->endereco);
				if (Reg[fetch->inst.rs1]==Reg[fetch->inst.rt1]) {
					z=1;
				}
				else {
					z=0;
				}
				if (sc->inversor==1) {
					if (z==1) {
						z=0;
					}
					else {
						z=1;
					}
				}
				OrigPc=(sc->branch && z);
				if (decode->OrigPC==2) {
					OrigPc=2;
				}
				else {
				}
				if (decode->OrigPC==3) {
					OrigPc=3;
				}
				decode->OrigPC=sc->origpc;
				if (sc->link==1) {
					reg[31]=fetch->endereco;
				}
				else {
				}
				if (OrigPc!=0) {
					branched=1;
				}
			}
		}
	}
	if (decode->LeMem==1 && ((decode->rt==fetch->inst.rs1) || (decode->rt==fetch->inst.rt1))) {
		stall=1;
		//printf("\nPermissão: %d \n",permissao_w);
		//printf("\nle mem: %d \n",decode->LeMem);
	}
}
int control_alu (int opALU, int funct) {
	int controle=0;
    switch (opALU) {
		case 0:
			controle=2;
            break;
		case 1:
            controle=6;
            break;
        case 2:
            switch (funct) {
				case 0:
                    controle=3;
                    break;
                case 2:
                    controle=4;
                    break;
				case 32:
					controle=2;
                    break;
                case 34:
                    controle=6;
                    break;
                case 36:
					controle=0;
                    break;
                case 37:
                    controle=1;
                    break;
				case 39:
					controle=5;
					break;
                case 42:
                    controle=7;
                    break;
				case 90:
					controle=8;
					break;
            }
			break;
		case 4:
			controle=1;
			break;
		case 3:
			controle=7;
			break;
        case 5:
            controle=2;
    }
    return controle;
}
int ULA (int a,int b,int cont_ula) {
	int c;
    switch (cont_ula) {
		case 0:
            c=(a&b);
            break;
		case 1:
			c=(a|b);
            break;
        case 2:
            c=(a+b);
            break;
        case 3:
			c=a<<b;
			break;
        case 4:
			c=a>>b;
			break;
        case 5:
			c=~(a|b);
			break;
        case 6:
			c=(a-b);
            break;
        case 7:
            if (a<b) {
				c=1;
			}
			else {
				c=0;
			}
            break;
		case 8:
			c=a*b;
			break;
    }
	//printf("\n%d+%d=%d\n",a,b,c);
    return c;
}
void Execute (ID_EX * decode,EX_MEM * execute, int Fcontrol) {
    int control_ula;

	execute->exit=decode->exit;
	if (execute->exit==1) {
	}
	else {
		execute->inst=decode->inst;
		execute->rs=decode->rs;
		execute->rt=decode->rt;
		execute->rd=decode->rd;
		execute->dado_w=decode->dado2;
		execute->EscreveReg=decode->EscreveReg;
		execute->LeMem=decode->LeMem;
		execute->EscreveMem=decode->EscreveMem;
		execute->MemparaReg=decode->MemparaReg;
		forward_control(decode, Fcontrol);
		execute->dado_wm=mux2(sinalmux2,execute->dado_w,execute->resultado);
		execute->destino=mux2(decode->RegDst,decode->rt,decode->rd);
		control_ula=control_alu(decode->OpAlu,decode->funct);
		execute->resultado=ULA(mux4(decode->OrigALU1,decode->dado1,execute->resultado,decode->deslocamento,dado_w),mux6(decode->OrigALU2,decode->dado2,extensao,execute->resultado,decode->shamt,0,dado_w),control_ula);
	}
	sinalmux2=0;
}
void Memory (EX_MEM * execute,MEM_WB * memory,int op1) {
	int cachemiss1,cachemiss2,endcache,x,i,j,k,bitsindice,endmem,tag,menor1,menor2;
	memory->exit=execute->exit;
	cachemiss1=1;
	cachemiss2=1;
	menor1=0;
	menor2=0;
	if (memory->exit==1) {
	}
	else {
		memory->inst=execute->inst;
		memory->rs=execute->rs;
		memory->rt=execute->rt;
		memory->rd=execute->rd;
		memory->EscreveReg=execute->EscreveReg;
		memory->MemparaReg=execute->MemparaReg;
		memory->destino=execute->destino;
		memory->resultado=execute->resultado;
		while (execute->LeMem==1) {
			switch (op1) {
				case 1:
					/*endcache=execute->resultado%(linha1);
					bitsindice=logaritmo(linha1);
					tag=execute->resultado>>bitsindice;
					while (cachemiss1==1) {
						for (i=0;i<2;i++) {			//Buscar na cache
							if (cachedado[endcache][i].v==1) {
								if (cachedado[endcache][i].tag==tag) {
									memory->dado_r=cachedado[endcache][i].dado;
									cachedado[endcache][i].r=1;
									if (i==0) {
										cachedado[endcache][1].r=0;
									}
									else {
										cachedado[endcache][0].r=0;
									}
									cachemiss1=0;
									i=3;
								}
							}
						}
						if (cachemiss1==1) {
							for (j=0;j<2;j++) {	//Buscar na memória
								if (cachedado[endcache][j].v==0) {
									cachedado[endcache][j].dado=data_memory[execute->resultado];
									cachedado[endcache][j].v=1;
									cachedado[endcache][j].r=1;
									cachedado[endcache][j].tag=execute->resultado>>bitsindice;
									if (j==0) {
										cachedado[endcache][1].r=0;
									}
									else {
										cachedado[endcache][0].r=0;
									}
									j=3;
									x=1;
								}
							}
							if (x==0) {
								for (j=0;j<2;j++) { //substituição
									if(cachedado[endcache][j].r==0) {
										if (cachedado[endcache][j].m==1) {
											endmem=tag<<bitsindice;
											endmem=endmem & endcache;
											data_memory[endmem]=cachedado[endcache][j].dado;
										}
										cachedado[endcache][j].dado=data_memory[execute->resultado];
										cachedado[endcache][j].r=1;
										cachedado[endcache][j].tag=execute->resultado>>bitsindice;
										if (j==0) {
											cachedado[endcache][1].r=0;
										}
										else {
											cachedado[endcache][0].r=0;
										}
										j=3;
										x=0;
									}
								}
							}
						}
					}*/
					endcache=execute->resultado%(linha1);;
				bitsindice=logaritmo(linha1);
				tag=execute->resultado>>bitsindice;
				while (cachemiss1==1) {
					for (i=0;i<2;i++) {			//Buscar na cache
						//printf("\ncachemiss2: %d \n",cachemiss1);
						if (cacheinst[endcache][i].v==1) {
							if (cacheinst[endcache][i].tag==tag) {
								memory->dado_r=cachedado[endcache][i].dado;
								cachedado[endcache][i].r=1;
								if (i==0) {
									cachedado[endcache][1].r=0;
								}
								else {
									cachedado[endcache][0].r=0;
								}
								cachemiss1=0;
								i=3;
							}
						}
					}
					if (cachemiss1==1) {
						for (j=0;j<2;j++) {	//Buscar na memória
							//printf("\nEstou aqui e sua validade é %d\n ", cachedado[endcache][j].v);
							if (cachedado[endcache][j].v==0){
								//printf("\ncachemiss: %d \n",cachemiss1);
								cachedado[endcache][j].dado=memory->dado_r;
								cachedado[endcache][j].v=1;
								//cachedado[endcache][j].m=0;
								cachedado[endcache][j].r=1;
								cachedado[endcache][j].tag=execute->resultado>>bitsindice;
								if (j==0) {
									cachedado[endcache][1].r=0;
								}
								else {
									cachedado[endcache][0].r=0;
								}
								j=3;
								x=1;

								cachemiss1=0;
								//printf("cachemiss de baixo %d", cachemiss1);
							}
							else x=0;
						}
						if (x==0) {
							//printf("x %d\n", x);
							for (j=0;j<2;j++) { //busca e substituição
								if(cachedado[endcache][j].r==0) {
									if (cachedado[endcache][j].m==1) {
										endmem=tag<<bitsindice;
										endmem=endmem & endcache;
										data_memory[endmem]=cachedado[endcache][j].dado;
										cachedado[endcache][j].m=0;
									}
									cachedado[endcache][j].dado=data_memory[execute->resultado];
									cachedado[endcache][j].tag=execute->resultado>>bitsindice;
									cachedado[endcache][j].r=1;
									if (j==0) {
										cachedado[endcache][1].r=0;
									}
									else {
										cachedado[endcache][0].r=0;
									}
									j=3;
									x=0;
									cachemiss1=0;
								}
							}
						}
					}
				}
					break;
				case 2:
					endcache=pc%(linha2);
					bitsindice=logaritmo(linha2);
					tag=pc>>bitsindice;
					while (cachemiss1==1) {
						for (i=0;i<4;i++) {			//Buscar na cache
							if (cachedado4[endcache][i].v==1) {
								if (cachedado4[endcache][i].tag==tag) {
									memory->dado_r=cachedado[endcache][i].dado;
									cachedado4[endcache][i].cont++;
									cachemiss1=0;
									i=4;
								}
							}
						}
						if (cachemiss1==1) {
							for (j=0;j<4;j++) {	//Buscar na memória
								if (cachedado4[endcache][j].v==0){
									memory->dado_r=cachedado4[endcache][j].dado;
									cachedado4[endcache][j].v=1;
									cachedado4[endcache][j].tag=pc>>bitsindice;
									cachedado4[endcache][j].cont++;
									j=4;
									x=1;
								}
								else x=0;
							}
							if (x==0) {
								for (j=0;j<4;j++) { //busca e substituição
									if(cachedado4[endcache][j].cont<menor1){
										menor1=cachedado4[endcache][j].cont;
									}
								}
								if (cachedado4[endcache][menor1].m==1) {
									endmem=tag<<bitsindice;
									endmem=endmem & endcache;
									memory->dado_r=cachedado[endcache][menor1].dado;
									cachedado4[endcache][menor1].m=0;
								}
								for(k=0;k<4;k++){
									cachedado4[endcache][k].cont=0;
								}
								cachedado[endcache][i].dado=memory->dado_r;
								cachedado4[endcache][menor1].tag=pc>>bitsindice;
								cachedado4[endcache][menor1].cont++;
								j=4;
								x=0;
							}
						}
					}
					break;
			}
			break;
		}
		while (execute->EscreveMem==1) {
			switch (op1) {
				case 1:
					endcache=execute->resultado%(linha1);
					bitsindice=logaritmo(linha1);
					tag=execute->resultado>>bitsindice;
					while (cachemiss2==1) {
						for (k=0;k<2;k++) {
							//printf("tag %d\n", tag);
							if(cachedado[endcache][k].tag==tag){
								cachedado[endcache][k].dado=execute->dado_wm;
								//printf(" comparacao das tags cachedado[%d][%d].dado %d\n",endcache,k, cachedado[endcache][k].dado);

								cachedado[endcache][k].m=1;
								cachemiss2=0;
								k=3;
							}
						}
						if(cachemiss2==1){
							for (i=0;i<2;i++) {			//Buscar na cache
								if (cachedado[endcache][i].v==0) {

									cachedado[endcache][i].dado=execute->dado_wm;
									cachedado[endcache][i].tag=execute->resultado>>bitsindice;

									//printf(" inserçao dado=execute->dado_wm %d \n",execute->dado_wm);
									//printf("cachedado[endcache][i].dado %d \n", cachedado[endcache][i].dado);
									cachedado[endcache][i].r=1;
									cachedado[endcache][i].v=1;
									if (i==0) {
										cachedado[endcache][1].r=0;
									}
									else {
										cachedado[endcache][0].r=0;
									}
									//cachemiss2=0;
									i=3;
									x=1;
								}
								else x=0;
							}
					//}
							if (x==0) {
								for (j=0;j<2;j++) { //substituição
									//printf(" substituicao cachedado[endcache][j].r %d", cachedado[endcache][j].r);
									if(cachedado[endcache][j].r==0) {
										//printf("modificaçao %d\n",cachedado[endcache][j].m);
										if (cachedado[endcache][j].m==1) {
											endmem=tag<<bitsindice;
											endmem=endmem & endcache;
											//printf(" endmem%d\n", endmem);
											data_memory[endmem]=cachedado[endcache][j].dado;
										}
										cachedado[endcache][j].dado=data_memory[execute->resultado];
										cachedado[endcache][j].r=1;
										cachedado[endcache][j].tag=execute->resultado>>bitsindice;
										if (j==0) {
											cachedado[endcache][1].r=0;
										}
										else {
											cachedado[endcache][0].r=0;
										}
										j=3;
									}
								}
							}
						}
					}
					//printf("Cachemiss2: %d \n",cachemiss2);
					break;
				case 2:
					endcache=execute->resultado%(linha1);
					bitsindice=logaritmo(linha1);
					tag=execute->resultado>>bitsindice;
					while (cachemiss2==1) {
						for (k=0;k<4;k++) {
							if(cachedado4[endcache][k].tag==tag){
								cachedado4[endcache][k].dado=execute->dado_wm;
								cachedado4[endcache][k].m=1;
								cachemiss2=0;
								k=4;
							}
						}
						if(cachemiss2==1){
							for (i=0;i<4;i++) {			//Buscar na cache
								if (cachedado4[endcache][i].v==0) {
									cachedado4[endcache][i].dado=execute->dado_wm;
									cachedado4[endcache][i].cont++;
									cachemiss2=0;
									i=5;
								}
							}
						}
					}
					if (cachemiss2==1) {
						for (j=0;j<4;j++) { //substituição
							if(cachedado4[endcache][j].cont<menor2){
								menor2=cachedado4[endcache][j].cont;
								if (cachedado4[endcache][menor2].m==0) {
									endmem=tag<<bitsindice;
									endmem=endmem & endcache;
									data_memory[endmem]=cachedado4[endcache][menor2].dado;
								}
								for(k=0;k<4;k++){
									cacheinst4[endcache][k].cont=0;
								}
								cachedado4[endcache][menor2].dado=data_memory[execute->resultado];
								cachedado4[endcache][menor2].tag=execute->resultado>>bitsindice;
								cachedado4[endcache][menor2].cont++;
								j=5;
							}
						}
					}
					break;
			}
			break;
		}
	}
}
int WriteBack (MEM_WB * memory) {
	int mux[2],destino;
	if (memory->exit==1) {
	}
	else {
		//mux[0]=memory->resultado;
		//mux[1]=memory->dado_r;
		//dado_w=mux[memory->MemparaReg];
		dado_w=mux2(memory->MemparaReg,memory->resultado,memory->dado_r);
		destino=memory->destino;
		if (memory->EscreveReg==1) {
			reg[destino]=dado_w;
		}
	}
	return memory->exit;
}
void inicializa_cacheL1 (CacheInstrucoes cache2[linha1][2]) {
	int i,j;
	for (i=0;i<linha1;i++) {
		for (j=0;j<2;j++) {
			cache2[i][j].v=0;
			cache2[i][j].r=0;
			cache2[i][j].m=0;
		}
	}
}
void inicializa_cacheL2 (CacheDados cache2[linha1][2]) {
	int i,j;
	for (i=0;i<linha1;i++) {
		for (j=0;j<2;j++) {
			cache2[i][j].v=0;
			cache2[i][j].r=0;
			cache2[i][j].m=0;
			cache2[i][j].tag=-1;
		}
	}
}
void inicializa_cache4L1 (CacheInstrucoes4 cache2[linha2][4]) {
	int i,j;
	for (i=0;i<linha2;i++) {
		for (j=0;j<4;j++) {
			cache2[i][j].v=0;
			cache2[i][j].cont=0;
			cache2[i][j].m=0;
		}
	}
}
void inicializa_cache4L2 (CacheDados4 cache2[linha2][4]) {
	int i,j;
	for (i=0;i<linha2;i++) {
		for (j=0;j<4;j++) {
			cache2[i][j].v=0;
			cache2[i][j].cont=0;
			cache2[i][j].m=0;
		}
	}
}
int menu1 () {
	int Fcontrol;
	printf("\nEstado do forward: \n");
	printf("1.Desativado\n");
	printf("2.Ativado\n");
	printf("Opção: ");
	scanf("%d",&Fcontrol);
	return Fcontrol;
}
int menu2 () {
	int op;
	printf("\nInforme a assossiatividade de cache: \n");
	printf("1.Cache assossiativa por 2 vias\n");
	printf("2.Cache assossiativa por 4 vias\n");
	printf("Opção: ");
	scanf("%d",&op);
	return op;
}
int main (int argc, char** argv) {
	strcpy(ARQ,argv[1]);
	printf("%s",ARQ);
	Instrucao x;
	int j;
	char inst[30];
	IF_ID fetch;
	ID_EX decode;
	EX_MEM execute;
	MEM_WB memory;
	inicializa_ram();
	inicializa_mdados();
	int exit=0;
	inicializa_pipeline(&fetch,&decode,&execute,&memory);
	int cont,op,op1;
	char nome[5];
	Sinais sc;
	op=menu1();
	op1=menu2();
	FILE *fp;
	FILE *disco;
	printf("%s", ARQ);
	fp=fopen(ARQ,"rt");

	disco=fopen("disco.eexe","wb");
	cont=0;
	extensao=0;
	pc=0;
	permissao_w=1;
	int pos;
	int i;
	sinalmux2=0;
	inicializa_cacheL1(cacheinst);
	inicializa_cacheL2(cachedado);
	inicializa_cache4L1(cacheinst4);
	inicializa_cache4L2(cachedado4);
	while (fscanf(fp," %[^\n]",inst)==1) {
		pos=0;
		if (inst[0]!='#') {
			for (i=0;i<30;i++) {
				if (inst[i]==':') {
					pos=i;
				}
				else {
				}
			}
			if (pos!=0) {
				for (i=0;i<30;i++) {
					inst[i]=inst[i+pos+2];
				}
			}
			filtro(inst,x,N,disco);
			cont++;
		}
	}
	fclose(disco);
	disco=fopen("disco.eexe","rb");
	carrega_memoria(disco,cont);
	inicializa(reg);
	imprime(reg);
	decode.sc.origpc=0;
	while (exit==0) {
		exit=WriteBack(&memory);
        Memory(&execute,&memory,op1);
		//imprime_cache_dados(cachedado);
		//imprime_mem_dados(data_memory);
        Execute(&decode,&execute,op);
		instruction_decode(&fetch,&decode,reg,&sc);
		instruction_fetch(&fetch,&decode,op1);
		print(&fetch,&decode,&execute,&memory);
		Hazard(&fetch,&decode,&execute,&memory);
		//imprime(reg);
		system("read");
		if (stall==1) {
			permissao_w=0;
		}
		else {
			permissao_w=1;
		}
	}
	fclose(fp);
	fclose(disco);
	imprime_cache_dados(cachedado);
	//imprime_mem(memoria,cont);
	imprime_mem_dados(data_memory);



	imprime(reg);
    return 0;
}













