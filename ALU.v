
    module mainAlu(Result,shift_amount,OP,Reg1,Reg2,zero);
        output reg signed [31:0] Result;
        output reg zero;
        input [4:0]shift_amount;
        input [3:0] OP;
        input signed [31:0] Reg1,Reg2;
        parameter[3:0] ADD = 4'b0001, SUB = 4'b0010, AND = 4'b0011, OR = 4'b0100, SLL = 4'b0101, SRl = 4'b0110,SRa = 4'b0111;
        always@( Reg1 or Reg2 or shift_amount or OP)
            begin
                case(OP)
                    ADD: Result <= (Reg1+Reg2);
                    SUB:
                        begin
                            Result <= (Reg1-Reg2);
                            if((Reg1-Reg2)==0) zero<=0;
                            else zero<=1;
                        end
                    AND: Result <= (Reg1&Reg2);
                    OR: Result <= (Reg1|Reg2);
                    SLL: Result <= (Reg1<<shift_amount); 
                    SRl: Result <= (Reg1>>shift_amount);
                    SRa: Result <= (Reg1>>>shift_amount);
                    // 4'b1000: Result <= (((Reg1-Reg2)>0)? 1:0);
                    // 4'b1001: Result <= (((Reg2-Reg1)>0)? 1:0);
                    // default: Result <= 0;
                endcase
            end
    endmodule

    module RegisterFile(read_reg1
                    ,read_reg2
                    ,write_reg
                    ,write_data
                    ,read_data1
                    ,read_data2
                    ,enable
                    ,clk);
        input [4:0] read_reg1,read_reg2,write_reg;
        input [31:0] write_data;
        input enable;
        input clk;
        output reg signed [31:0] read_data1,read_data2;

        reg [31:0] Registers [0:31];

        initial begin
            Registers[0]  <= 32'h00000000;
            Registers[1]  <= 32'h00000001;
            Registers[2]  <= 32'h00000002;
            Registers[3]  <= 32'h00000003;
            Registers[4]  <= 32'h00000004;
            Registers[5]  <= 32'h00000005;
            Registers[6]  <= 32'h00000006;
            Registers[7]  <= 32'h00000007;
            Registers[8]  <= 32'h00000008;
            Registers[9]  <= 32'h00000009;
            Registers[10] <= 32'h0000000a;
            Registers[11] <= 32'h0000000b;
            Registers[12] <= 32'h0000000c;
            Registers[13] <= 32'h0000000d;
            Registers[14] <= 32'h0000000e;
            Registers[15] <= 32'h0000000f;
            Registers[16] <= 32'h00000010;
            Registers[17] <= 32'h00000011;
            Registers[18] <= 32'h00000012;
            Registers[19] <= 32'h00000013;
            Registers[20] <= 32'h00000014;
            Registers[21] <= 32'h00000015;
            Registers[22] <= 32'h00000016;
            Registers[23] <= 32'h00000017;
            Registers[24] <= 32'h00000018;
            Registers[25] <= 32'h00000019;
            Registers[26] <= 32'h0000001a;
            Registers[27] <= 32'h0000001b;
            Registers[28] <= 32'h0000001c;
            Registers[29] <= 32'h0000001d;
            Registers[30] <= 32'd252;
            Registers[31] <= 32'b0;
        end
        always@(posedge clk)
        begin
            if (enable) 
                begin
                    Registers[write_reg] <= write_data;
                end
            read_data1 <= Registers[read_reg1];
            read_data2 <= Registers[read_reg2];
        end
    endmodule

    module MemtoRegMux(output reg signed[31:0] data ,input selector ,input signed [31:0] input1 ,input signed [31:0] input2);
        always@(selector,input1,input2)
            begin
                case(selector)
                    0: data <= input1;
                    1: data <= input2;
                endcase
            end
    endmodule

    module ALUOperand2Mux(output reg [31:0] data ,input[1:0] selector ,input  [31:0] input1 ,input [31:0] input2 , input [31:0] input3);
        always@(selector,input1,input2,input3)
            begin
                case(selector)
                    0: data <= input1;
                    1: data <= input2;
                    2: data <= input3;
                endcase
            end
    endmodule

    module ALUOperand1Mux(output reg [31:0] data ,input[1:0] selector ,input  [31:0] input1 ,input [31:0] input2 , input [31:0] input3);
        always@(selector,input1,input2,input3)
            begin
                case(selector)
                    0: data <= input1;
                    1: data <= input2;
                    2: data <= input3;
                endcase
            end
    endmodule


    module RegDstMux(output reg [4:0] data ,input selector ,input  [4:0] input1 ,input  [4:0] input2);
        always@(selector,input1,input2)
            begin
                case(selector)
                    0: data <= input1;
                    1: data <= input2;
                endcase
            end
    endmodule

    module PCSrcMux(output reg [31:0] data ,input[1:0] selector ,input  [31:0] input1 ,input  [31:0] input2 ,input  [31:0]  input3);
        always@(selector)
            begin
                case(selector)
                    2'b00: data <= input1;
                    2'b01: data <= input2;
                    2'b10: data <= input3;
                    default : data <= input1;
                endcase
            end
    endmodule

    module pcIncreamentAlu(Result,PC);
        output reg [31:0] Result;
        input [31:0] PC;
        always@(PC)
            begin
                Result<=PC+32'd4;
            end
    endmodule
    
    module pcBeqAdderAlu(Result,input1,input2);
        output reg [31:0] Result;
        input [31:0] input1;
        input signed [31:0]  input2;
        always@(input1,input2)
            begin
                Result<=input1+(input2<<2);
            end
    endmodule

    module instructionMemory(readAddress,instruction,clk);
        input [31:0] readAddress;
        output reg signed [31:0] instruction;
        reg [31:0] Registers [1023:0];
        input clk;
        initial
        begin
            Registers[0] <= 32'h02328020;
            Registers[1] <= 32'h02538820;
            Registers[2] <= 32'h02749020;
            Registers[3] <= 32'h02959820;
            Registers[4] <= 32'h02b6a020;
        end
        always @(posedge clk)
            begin
                instruction<=Registers[readAddress[9:2]];
            end
    endmodule

    module PC(On,in,out);
        input [31:0] in;
        output reg [31:0] out;
        input On;
        initial begin out<=0; end
        always@(in)
        begin
            if(On)
                begin
                    out<=in;
                end
        end
    endmodule

    module signExtend(in,out);
      input signed [15:0] in;
      output reg signed [31:0]  out;
      always @(in)
        begin
            out <= {{16{in[15]}},in};
        end  
    endmodule

    module dataMemory(address,readData,writeData,readEnable,writeEnable,clk);
        input readEnable,writeEnable;
        input [31:0] address;
        input [31:0] writeData;
        output reg signed [31:0] readData;
        reg [7:0] Registers [4194304:0];
        input clk;
        always @(posedge clk)
            begin
                if(readEnable)
                    begin 
                        readData<={Registers[address[7:0]], Registers[address[7:0]+1]
                                 , Registers[address[7:0]+2], Registers[address[7:0]+3]};
                    end
                if(writeEnable)
                    begin
                        Registers[address[7:0]] <= writeData[31:24];
                        Registers[address[7:0]+1] <= writeData[23:16];
                        Registers[address[7:0]+2] <= writeData[15:8];
                        Registers[address[7:0]+3] <= writeData[7:0];
                    end
            end
    endmodule

    module mainControlUnit(opCode, RegDst, Branch, MemRead, MemtoReg, ALUOp, MemWrite, ALUSrc, RegWrite);
        input [5:0] opCode;
        output reg RegDst, Branch, MemRead, MemtoReg, MemWrite, ALUSrc, RegWrite;
        output reg[1:0] ALUOp;
        parameter[5:0] aluoperation = 6'b000000 , sw=6'b101011 , lw= 6'b100011 ,beq = 6'b000100 ;
        always@*
        begin
            case(opCode)
                aluoperation:
                    begin
                        RegDst = 1;
                        ALUSrc = 0 ;
                        MemtoReg = 0;
                        RegWrite = 1;
                        MemRead = 0;
                        MemWrite = 0;
                        Branch = 0;
                        ALUOp=2'b10;
                    end
                lw:
                    begin
                        RegDst = 0;
                        ALUSrc = 1 ;
                        MemtoReg = 1;
                        RegWrite = 1;
                        MemRead = 1;
                        MemWrite = 0;
                        Branch = 0;
                        ALUOp=2'b00;
                    end
                sw:
                    begin
                        RegDst = 0;
                        ALUSrc = 1;
                        MemtoReg = 0;
                        RegWrite = 0;
                        MemRead = 0;
                        MemWrite = 1;
                        Branch = 0;
                        ALUOp=2'b00;
                    end
                beq:
                    begin
                        RegDst = 0;
                        ALUSrc = 0;
                        MemtoReg = 0;
                        RegWrite = 0;
                        MemRead = 0;
                        MemWrite = 0;
                        Branch = 1;
                        ALUOp=2'b01;
                    end
            endcase
        end
    endmodule

    module aluControlUnit(ALUOp,funct,op);
        input [1:0] ALUOp;
        input [5:0] funct;
        output reg [3:0] op;
        parameter[3:0] ADD = 4'b0001, SUB = 4'b0010, AND = 4'b0011, OR = 4'b0100, SLL = 4'b0101, SRl = 4'b0110,SRa = 4'b0111;
        always@*
            begin
                case(ALUOp)
                    2'b00:op<=ADD;
                    2'b01:op<=SUB;
                    2'b10:
                        begin
                            case(funct)
                                6'b100000:op<=ADD;
                                6'b100010:op<=SUB;
                                6'b100100:op<=AND;
                                6'b100101:op<=OR;
                                6'b000000:op<=SLL;
                            endcase
                        end
                endcase
            end
    endmodule

    module forwardingUnit(IdExRtReg,IdExRsReg,forwardA,forwardB,ExMemRdReg,ExMemWB,MemWbWb,MemWbRdReg);
        input [4:0] IdExRtReg,IdExRsReg,ExMemRdReg,MemWbRdReg;
        input ExMemWB,MemWbWb;
        output reg[1:0] forwardA,forwardB;

        always@(IdExRtReg,IdExRsReg ,ExMemRdReg,ExMemWB,MemWbWb,MemWbRdReg)
        begin
            if(ExMemWB &&(ExMemRdReg != 0) && ( ExMemRdReg == IdExRsReg)) forwardA<=2'd2;
            else if(MemWbWb &&(MemWbRdReg != 0) &&!((ExMemWB &&(ExMemRdReg != 0) && ( ExMemRdReg == IdExRsReg))) && ( MemWbRdReg == IdExRsReg)) forwardA<=2'd1;
            else forwardA<=2'd0;

            if(ExMemWB &&(ExMemRdReg != 0) && ( ExMemRdReg == IdExRtReg)) forwardB<=2;
            else if (MemWbWb &&(MemWbRdReg != 0) && !(ExMemWB &&(ExMemRdReg != 0) && ( ExMemRdReg == IdExRtReg))  && ( MemWbRdReg == IdExRtReg)) forwardB<=1;
            else forwardB<=0;
        end
    endmodule

    module dataHazardMux(input[8:0] in, output reg[8:0]  out,input selector);
        always@(selector,in)
            begin
                if(selector)
                    begin out<=in; end
                else begin out<=8'h00; end
            end
    endmodule
    
    module hazardDetectionUnit(IdExMemRead,IdExRtReg,IfIdRsReg,IfIdRtReg,IFOn,PCOn,dataHazardMuxCtrl);
        output reg IFOn,PCOn,dataHazardMuxCtrl;
        input IdExMemRead;
        input [4:0] IdExRtReg,IfIdRsReg,IfIdRtReg;
        initial
        begin
            IFOn<=1;
            PCOn<=1;
            dataHazardMuxCtrl<=1;
        end
        always@(IdExMemRead,IdExRtReg,IfIdRsReg,IfIdRtReg)
        begin
            if(IdExMemRead && ((IdExRtReg == IfIdRtReg)||(IdExRtReg == IfIdRsReg))) 
            begin
                IFOn<=0;
                PCOn<=0;
                dataHazardMuxCtrl<=0;
            end
            else
            begin
                IFOn<=1;
                PCOn<=1;
                dataHazardMuxCtrl<=1;
            end
        end
    endmodule

    module Branch(output reg out, input [31:0] in1 , in2);
        always@(in1,in2) begin out<= ((in1-in2)==32'h00000000)? 1:0; end
    endmodule

    module AND(output wire out, input in1,in2);
            assign out= in1&in2;
    endmodule


    module Processor(clk,IFIDOn,PCOn, IFID,IDEX,EXMEM,MEMWB,pcIn,pcOut,instruction,dataHazardMuxOutput,signExtendOutput ,regFileData1,regFileData2,mainAluInput1,mainAluInput2
                    ,mainAluResult,PcIncreamentAluResult,PcBeqAdderAluResult,regFileWriteData
                    ,dataMemoryReadData,regFileWriteReg,regdst,branch,memread,alucontrolOutput
                    ,memtoreg,memwrite,alusrc,regwrite,Zero,dataHazardCtrl,aluop,ForwardA,ForwardB);


        output wire IFIDOn,PCOn ;
        output reg [63:0] IFID;
        output  reg [119:0] IDEX;
        output reg [78:0] EXMEM;
        output  reg [70:0] MEMWB;
        output wire[8:0] dataHazardMuxOutput;
        output wire [31:0] signExtendOutput ,regFileData1,regFileData2,mainAluInput1,mainAluInput2
                    ,mainAluResult,PcIncreamentAluResult,PcBeqAdderAluResult,regFileWriteData
                    ,dataMemoryReadData;
        output wire [31:0]pcOut,instruction;
        output wire [31:0]pcIn;
        output wire [4:0] regFileWriteReg;
        output wire regdst,branch,memread,memtoreg,memwrite,alusrc,regwrite,Zero,dataHazardCtrl;
        output wire [1:0]aluop,ForwardA,ForwardB;
        output wire [3:0] alucontrolOutput;
       wire  pCSrcMuxSelector;
        
        input clk;
        always@(posedge clk)
            begin
                 IFID<={PcIncreamentAluResult,instruction}; 
                
                IDEX<={dataHazardMuxOutput/*119-111 */,regFileData1/*110-79 */,regFileData2/*78-47 */
                        ,signExtendOutput /*46-15 */,IFID[25:11]/*14-0 */};
                
                EXMEM<={Zero,IDEX[119:111]/*77-69*/,mainAluResult/*68-37*/,mainAluInput2 /*36-5*/,regFileWriteReg/*4-0*/};//get that stupid mux output
                
                MEMWB<={EXMEM[74]/*70 memtoreg*/
                        ,EXMEM[70]/*69 regWriteSignal*/
                        ,dataMemoryReadData/*68-37*/
                        ,EXMEM[68:37]/*36-5  AluResult*/
                        ,EXMEM[4:0]/*4-0  WriteReg*/};
            end

        Branch myBranch(.out(Zero),.in1(regFileData1),.in2(regFileData2));

        AND myAnd(.out(pCSrcMuxSelector),.in1(Zero),.in2(branch));

        aluControlUnit AluControlUnit(.ALUOp(IDEX[115:114]),.funct(IDEX[20:15]),.op(alucontrolOutput));
        //Finished

        mainControlUnit MainControlUnit(.opCode(IFID[31:26]), .RegDst(regdst), .Branch(branch), .MemRead(memread), .MemtoReg(memtoreg)
                                        ,.ALUOp(aluop), .MemWrite(memwrite),. ALUSrc(alusrc), .RegWrite(regwrite));
        //Finished

        dataMemory DataMemory(.address(EXMEM[68:37]),.readData(dataMemoryReadData)
                            ,.writeData(EXMEM[68:37]),.readEnable(EXMEM[75]),.writeEnable(EXMEM[71]));
        //CLOCK Remains

        signExtend SignExtend(.in(IFID[15:0]),.out(signExtendOutput));
        //Finished

        PC pc(.On(PCOn),.in(pcIn),.out(pcOut));
        //Finished

        instructionMemory InstructionMemory(.readAddress(pcOut),.instruction(instruction));
        //CLOCK Remains

        pcBeqAdderAlu PcBeqAdderAlu(.Result(PcBeqAdderAluResult),.input1(IFID[63:32]),.input2(signExtendOutput));
        //Finished

        pcIncreamentAlu PcIncreamentAlu(.Result(PcIncreamentAluResult),.PC(pcOut));
        //Finished

        PCSrcMux pCSrcMux(.data(pcIn),.selector({{1'b0},pCSrcMuxSelector}), .input1(PcIncreamentAluResult), .input2(PcBeqAdderAluResult) , .input3(32'd0 ));
        //NOOOOOOOOOOOO

        RegDstMux regDstMux(.data(regFileWriteReg),.selector(IDEX[119]), .input1(IDEX[14:10]), .input2(IDEX[9:5]));
        //Finished

        ALUOperand1Mux ALUOperand1Mux(.data(mainAluInput1),.selector(ForwardA), .input1(IDEX[110:79]), .input2(regFileWriteData), .input3(EXMEM[68:37]));

        ALUOperand2Mux ALUOperand2Mux(.data(mainAluInput2),.selector(ForwardB), .input1(IDEX[78:47]), .input2(EXMEM[68:37]), .input3(regFileWriteData ));
        //NOOOOOOOOOOOO


        dataHazardMux DataHazardMux( .in({regdst,branch,memread,memtoreg,aluop,memwrite,alusrc,regwrite}), .out(dataHazardMuxOutput),.selector(dataHazardCtrl));

        MemtoRegMux memtoRegMux(.data(regFileWriteData),.selector(MEMWB[70]), .input1(MEMWB[68:37]), .input2(MEMWB[36:5]));
        //Finished

        hazardDetectionUnit HazardDetectionUnit(.IdExMemRead(IDEX[117]),.IdExRtReg(IDEX[9:5] ),.IfIdRsReg(IFID[25:21]),.IfIdRtReg(IFID[20:16]),.IFOn(IFIDOn),.PCOn(PCOn),.dataHazardMuxCtrl(dataHazardCtrl));

        mainAlu MainAlu(.Result(mainAluResult), .shift_amount(IDEX[25:21]), .OP(alucontrolOutput), .Reg1(mainAluInput1), .Reg2(mainAluInput2),.zero(zero));
        //Zero

        RegisterFile registerFile(.read_reg1(IFID[25:21]),.read_reg2(IFID[20:16]),.write_reg(MEMWB[4:0])
                                ,.write_data(regFileWriteData),.read_data1(regFileData1),.read_data2(regFileData2),.enable(MEMWB[69]));
        //CLOCK Remains

        forwardingUnit ForwardingUnit(.IdExRtReg(IDEX[9:5]),.IdExRsReg(IDEX[14:10]),.forwardA(ForwardA),.forwardB(ForwardB),.ExMemRdReg(EXMEM[4:0]),.ExMemWB(EXMEM[69]),.MemWbWb(MEMWB[69]),.MemWbRdReg(MEMWB[4:0]));

    endmodule

    module Test();

        wire IFIDOn,PCOn ;
        wire [63:0] IFID;
        wire [119:0] IDEX;
        wire [78:0] EXMEM;
        wire [70:0] MEMWB;
        wire[8:0] dataHazardMuxOutput;
        wire [31:0] signExtendOutput ,regFileData1,regFileData2,mainAluInput1,mainAluInput2
                    ,mainAluResult,PcIncreamentAluResult,PcBeqAdderAluResult,regFileWriteData
                    ,dataMemoryReadData;
        wire [31:0]pcOut,instruction;
        wire [31:0]pcIn;
        wire [4:0] regFileWriteReg;
        wire regdst,branch,memread,memtoreg,memwrite,alusrc,regwrite,Zero,dataHazardCtrl;
        wire [1:0]aluop,ForwardA,ForwardB;
        wire [3:0] alucontrolOutput;
        wire pCSrcMuxSelector; 
        reg clk;

        initial
            begin
                $monitor("IFIDOn = %h \n ,PCOn = %b \n , IFID = %b \n ,IDEX = %b \n ,EXMEM = %b \n ,MEMWB = %b \n ,pcIn = %h \n ,pcOut = %h \n ,instruction = %h \n    ,regFileData1 = %b \n ,regFileData2 = %b \n ,mainAluInput1 = %b \n ,mainAluInput2 = %b \n ,mainAluResult = %b \n ,PcIncreamentAluResult = %h \n ,PcBeqAdderAluResult = %h \n ,regFileWriteData = %h \n ,dataMemoryReadData = %h \n ,regFileWriteReg = %h \n ,regdst = %h \n ,branch = %h \n ,memread = %h \n ,alucontrolOutput = %h \n ,pCSrcMuxSelector = %h \n ,memtoreg = %h \n ,memwrite = %h \n ,alusrc = %h \n ,regwrite = %h \n ,Zero = %h \n ,dataHazardCtrl = %h \n ,aluop = %h \n ,ForwardA = %h \n ,ForwardB = %h \n )"
                        ,IFIDOn,PCOn, IFID,IDEX,EXMEM,MEMWB,pcIn,pcOut,instruction,dataHazardMuxOutput,signExtendOutput ,regFileData1,regFileData2,mainAluInput1,mainAluInput2,mainAluResult,PcIncreamentAluResult,PcBeqAdderAluResult,regFileWriteData,dataMemoryReadData,regFileWriteReg,regdst,branch,memread,alucontrolOutput,memtoreg,memwrite,alusrc,regwrite,Zero,dataHazardCtrl,aluop,ForwardA,ForwardB);
                clk= 0;
                #19
                $display("First Clok");
                #19
                $display("second Clok");

                #19
                $display("third Clok");

                #19
                $display("4th Clok");

                #19
                $display("5th Clok");

            end
            always
                begin
                #20 clk=~clk;
                end
        Processor processor(.clk(clk),.IFIDOn(IFIDOn),.PCOn(PCOn),. IFID(IFID),.IDEX(IDEX),.EXMEM(EXMEM),.MEMWB(MEMWB)
                            ,.pcIn(pcIn),.pcOut(pcOut),.instruction(instruction),.dataHazardMuxOutput(dataHazardMuxOutput),.signExtendOutput(signExtendOutput) 
                            ,.regFileData1(regFileData1),.regFileData2(regFileData2),.mainAluInput1(mainAluInput1),.mainAluInput2(mainAluInput2)
                            ,.mainAluResult(mainAluResult),.PcIncreamentAluResult(PcIncreamentAluResult),.PcBeqAdderAluResult(PcBeqAdderAluResult)
                            ,.regFileWriteData(regFileWriteData),.dataMemoryReadData(dataMemoryReadData),.regFileWriteReg(regFileWriteReg)
                            ,.regdst(regdst),.branch(branch),.memread(memread),.alucontrolOutput(alucontrolOutput)
                            ,.memtoreg(memtoreg),.memwrite(memwrite),.alusrc(alusrc),.regwrite(regwrite)
                            ,.Zero(Zero),.dataHazardCtrl(dataHazardCtrl),.aluop(aluop),.ForwardA(ForwardA),.ForwardB(ForwardB));
    endmodule
    
        module testPC();
        reg [31:0] PcIncreamentAluResult,PcBeqAdderAluResult;
        wire [31:0]pcOut;
        wire [31:0]pcIn;

        initial
            begin
                $monitor("pcIn=%b \n pcOut =%b \n   PcIncreamentAluResult=%b \n PcBeqAdderAluResult=%b \n "
                        ,pcIn,pcOut,PcIncreamentAluResult,PcBeqAdderAluResult);
                PcIncreamentAluResult<=32'hxxxxxxxx;
                PcBeqAdderAluResult<=32'hxxxxxxxx;

                #10
                PcIncreamentAluResult<=32'd1;
                PcBeqAdderAluResult<=32'hxxxxxxxx;
            end
        PC pc(.On(1'b1),.in(pcIn),.out(pcOut));
        PCSrcMux pCSrcMux(.data(pcIn),.selector(2'b0x), .input1(PcIncreamentAluResult), .input2(PcBeqAdderAluResult) , .input3(32'b0 ));

    endmodule
    module TestDataMemory();
        reg clk;
        reg [31:0]Address;
        wire [31:0]dataMemoryReadData;
        initial
            begin
                $monitor("Address = %h   data = %h");
                clk <=0 ;
                Address <=1'd0;
                #9

                Address <=1'd1;

                #9
                $display("second Clok");
                Address <=1'd2;

                #9
                $display("third Clok");
                Address <=1'd3;

            end

            dataMemory DataMemory(.address(Address),.readData(dataMemoryReadData)
                            ,.writeData(0),.readEnable(1),.writeEnable(0));

    endmodule
    // module TestControlUnits();

    //     wire regdst,branch,memread,memtoreg,memwrite,alusrc,regwrite;
    //     wire [1:0]aluop;
    //     reg  [31:0] instruction;
    //     wire [3:0] alucontrolOutput;
    //     initial
    //         begin
    //             $monitor("instruction[31:26] = %b, regdst = %b,branch = %b,memread = %b,memtoreg = %b,aluop = %b,memwrite = %b,alusrc = %b,regwrite  = %b",instruction[31:26],regdst,branch,memread,memtoreg,aluop,memwrite,alusrc,regwrite);
    //             $monitor("funct=%d , op= %b" ,instruction[5:0], alucontrolOutput);

    //             $display("R-Type ADD");
    //             instruction <=32'h00000020 ;
    //             #5
    //             $display("R-Type SUB");
    //             instruction <=32'h00000022 ;
    //             #5
    //             $display("R-Type AND");
    //             instruction <=32'h00000024 ;
    //             #5
    //             $display("R-Type OR");
    //             instruction <=32'h00000025 ;
    //             #5
    //             $display("R-Type SLL");
    //             instruction <=32'h00000000;
    //             #5
    //             $display("LW instruction");
    //             //LW instruction
    //             instruction <=32'h8C000000 ;
    //             #5
    //             $display("SW instruction");
    //             //SW instruction
    //             instruction <=32'hAC000000 ;
    //             #5
    //             $display("Beq Instruction");
    //             //Beq Instruction
    //             instruction <=32'h10000000 ;
    //         end
    //     mainControlUnit MainControlUnit(.opCode(instruction[31:26]), .RegDst(regdst), .Branch(branch), .MemRead(memread), .MemtoReg(memtoreg)
    //                                     ,.ALUOp(aluop), .MemWrite(memwrite),. ALUSrc(alusrc), .RegWrite(regwrite));
    //     aluControlUnit AluControlUnit(.ALUOp(aluop),.funct(instruction[5:0]),.op(alucontrolOutput));
    // endmodule



    // module TestMainControlUnit();

    //     wire regdst,branch,memread,memtoreg,memwrite,alusrc,regwrite;
    //     wire [1:0]aluop;
    //     reg  [31:0] instruction;
    //     initial
    //         begin
    //             $monitor("instruction[31:26] = %b, regdst = %b,branch = %b,memread = %b,memtoreg = %b,aluop = %b,memwrite = %b,alusrc = %b,regwrite  = %b",instruction[31:26],regdst,branch,memread,memtoreg,aluop,memwrite,alusrc,regwrite);
    //             //R-Type
    //             instruction <=32'h00000000 ;
    //             #5
    //             //LW instruction
    //             instruction <=32'h8C000000 ;
    //             #5
    //             //SW instruction
    //             instruction <=32'hAC00abcd ;
    //             #5
    //             //Beq Instruction
    //             instruction <=32'h10000000 ;
    //         end
    //     mainControlUnit MainControlUnit(.opCode(instruction[31:26]), .RegDst(regdst), .Branch(branch), .MemRead(memread), .MemtoReg(memtoreg)
    //                                     ,.ALUOp(aluop), .MemWrite(memwrite),. ALUSrc(alusrc), .RegWrite(regwrite));
    // endmodule






    // module TestPCplusBeqAdd();
    //     reg[31:0] pc1,pc2;
    //     wire[31:0] res;
        
    //     initial
    //         begin
    //             $monitor("PC1 value =%d + PC2 Value=%d   Result value =%d ",pc1,pc2,res);
    //             pc1 <=32'd1024 ;
    //             pc2 <=32'd1;
    //         end
    //                 pcBeqAdderAlu mine(.Result(res),.input1(pc1),.input2(pc2));
    // endmodule




    // module TestPCADDER();
    //     reg[31:0] pc;
    //     wire[31:0] res;
        
    //     initial
    //         begin
    //             $monitor("PC value =%d    Result value =%d ",pc,res);
    //             pc <=0 ;
    //             #5
    //                 pc<=1024;
    //             #10
    //                 pc<=1000;
    //         end
    //                 pcIncreamentAlu mine(.Result(res),.PC(pc));
    // endmodule







// module wholecircuit(readreg1
//                     ,readreg2
//                     ,writereg
//                     ,external_data
//                     ,mux_ctrl
//                     ,write_enable
//                     ,shift_amount
//                     ,op
//                     ,clk
//                     ,Result);
    
//     input [4:0] readreg1,readreg2,writereg;
//     input wire mux_ctrl,write_enable;
//     input wire [4:0]shift_amount;
//     input wire [3:0] op;
//     input wire clk;
//     input wire signed [31:0] external_data;

//     output reg signed  [31:0] Result ;

//     wire [31:0] res;
//     wire [31:0]writeData;
//     wire [31:0]readData1,readData2;
//     Mux myMux(writeData,mux_ctrl,external_data,res);
//     Register regFile(readreg1,readreg2,writereg,writeData,readData1,readData2,write_enable,clk);
//     ALU myAlu(res,shift_amount,op,readData1,readData2);
//     always @* begin
//      Result <= res;
//     end
// endmodule

// module TestAlu();
//     reg signed [31:0] Reg1,Reg2;
//     reg[3:0] OP;
//     reg [4:0]shift;
//     wire signed [31:0] Result;

//     initial
//         begin
//             $monitor("Reg1= %d Reg2=%d Result = %d",Reg1,Reg2,Result);
//             $display("\n          Addition Testing \n");
//             #0 //Addition  Result 13
//             Reg1 <=8;
//             Reg2 <=5;
//             OP = 4'b0001;
//             $display(" \naddition test with 5 + 8 = 13");

//             #10 //Addition  Result 13
//             Reg1 <=-8;
//             Reg2 <=-5;
//             OP = 4'b0001;
//             $display(" \naddition test with -5 + -8 = -13");

//             #20 //Addition  Result 13
//             Reg1 <=-8;
//             Reg2 <=5;
//             OP = 4'b0001;
//             $display(" \naddition test with 5 + -8 = -3 ");

//     ////////////////////////////////////////////////////////////////////////

//             #30 // Subtraction  Result 3
//             Reg1 <=8;
//             Reg2 <=5;
//             OP = 4'b0010;
//             $display("////////////////////////////////////////////////////////////////////////");

//             $display("\n          Subtraction Testing \n");

//             $display("subtraction test with 8 - 5 = 3");

//             #40 // Subtraction  Result 3
//             Reg1 <=-8;
//             Reg2 <=-5;
//             OP = 4'b0010;
//             $display("subtraction test with -8 - (-5) = -3");

//             #50 // Subtraction  Result 3
//             Reg1 <=-8;
//             Reg2 <=5;
//             OP = 4'b0010;
//             $display("subtraction test with -8 - 5 = -13");

//     ////////////////////////////////////////////////////////////////////////

//             #60 //AND  Result 1
//             Reg1 <=1;
//             Reg2 <=1;
//             OP = 4'b0011;
//             $display("////////////////////////////////////////////////////////////////////////");

//             $display("\n          AND Testing \n");

//             $display("AND test with 1 AND 1 = 1");

//             #70 //AND  Result 1
//             Reg1 <=0;
//             Reg2 <=1;
//             OP = 4'b0011;
//             $display("AND test with 0 AND 1 = 0");

//             #80 //AND  Result 1
//             Reg1 <=0;
//             Reg2 <=-1;
//             OP = 4'b0011;
//             $display("AND test with 0 AND -1 = 0");

//             #90 //AND  Result 1
//             Reg1 <=-1;
//             Reg2 <=-1;
//             OP = 4'b0011;
//             $display("AND test with -1 AND -1 = -1");

//     ////////////////////////////////////////////////////////////////////////

//             #100 // OR  Result 3
//             Reg1 <=1;
//             Reg2 <=1;
//             OP = 4'b0100;
//             $display("////////////////////////////////////////////////////////////////////////");

//             $display("\n          OR Testing \n");

//             $display("OR test with 1 OR 1  = 1");

//             #110 // OR  Result 3
//             Reg1 <=0;
//             Reg2 <=1;
//             OP = 4'b0100;
//             $display("OR test with 0 OR 1  = 1");

//             #120 // OR  Result 3
//             Reg1 <=0;
//             Reg2 <=0;
//             OP = 4'b0100;
//             $display("OR test with 0 OR 0  = 0");

//             #130 // OR  Result 3
//             Reg1 <=0;
//             Reg2 <=-1;
//             OP = 4'b0100;
//             $display("OR test with 0 OR -1  = -1");

//             #140 // OR  Result 3
//             Reg1 <=-1;
//             Reg2 <=-1;
//             OP = 4'b0100;
//             $display("OR test with -1 OR -1  = -1");

//     ////////////////////////////////////////////////////////////////////////

//             #150  //Shift Left Result 16
//             Reg1 <=8;
//             Reg2 <=0;
//             shift <=1;
//             OP = 4'b0101;
//             $display("////////////////////////////////////////////////////////////////////////");

//             $display("\n          Left Shifting Testing \n");

//             $display("ShiftLeft test with 8 shift_amount 1 = 16");

//             #160  //Shift Left Result 16
//             Reg1 <=-16;
//             Reg2 <=0;
//             shift <=1;
//             OP = 4'b0101;
//             $display(" \nShiftLeft test with -16 shift_amount 1 = -32");

//     ////////////////////////////////////////////////////////////////////////

//             #170  //Shift Right Result 2
//             Reg1 <=8;
//             Reg2 <=0;
//             shift <=2;
//             OP = 4'b0110;
//             $display("////////////////////////////////////////////////////////////////////////");

//             $display("\n          Right Shifting Testing \n");

//             $display("ShiftRight test with 8 and shift_amount 2 = 2");

//     ////////////////////////////////////////////////////////////////////////

//             #180  //Shift Right Arithmatic Result 1
//             Reg1 <=20;
//             Reg2 <=1;
//             shift <=2;
//             OP = 4'b0111;
//             $display("////////////////////////////////////////////////////////////////////////");

//             $display("\n          arithmatic Right Shifting Testing \n");

//             $display("ShiftRight arith test with 20 and shift_amount 2 = 5");

//             #190
//             Reg1 <=-20;
//             Reg2 <=1;
//             shift <=2;
//             OP = 4'b0111;
//             $display("ShiftRight arith test with -20 and shift_amount 2 = -5");

//     ////////////////////////////////////////////////////////////////////////

//             #200  //Greater Than Result 1
//             Reg1 <=7;
//             Reg2 <=8;
//             OP = 4'b1000;
//             $display("////////////////////////////////////////////////////////////////////////");

//             $display("\n          Greater than Testing \n");

//             $display("greater than test with 7>8 = false(0)");

//             #210  //Greater Than Result 1
//             Reg1 <=-7;
//             Reg2 <=-8;
//             OP = 4'b1000;
//             $display("greater than test with -7>-8 = true(1)");

//             #220  //Greater Than Result 1
//             Reg1 <=-8;
//             Reg2 <=7;
//             OP = 4'b1000;
//             $display("greater than test with -8>7 = false(0)");

//     ////////////////////////////////////////////////////////////////////////

//             #230  //Less than Result 1
//             Reg1 <=7;
//             Reg2 <=15;
//             OP = 4'b1001;
//             $display("////////////////////////////////////////////////////////////////////////");

//             $display("\n          Less than Testing \n");

//             $display("Less than test with 7<15 = true(1)");

//             #240  //Less than Result 1
//             Reg1 <=-7;
//             Reg2 <=-15;
//             OP = 4'b1001;
//             $display("Less than test with -7<-15 = false(0)");
//             #250  //Less than Result 1
//             Reg1 <=-7;
//             Reg2 <=15;
//             OP = 4'b1001;
//             $display("Less than test with -7<15 = true(1)");
//             #260  //Less than Result 1
//             Reg1 <=-15;
//             Reg2 <=-14;
//             OP = 4'b1001;
//             $display("Less than test with -15<-14 = true(1)");
//         end
//     ALU myalu(Result,shift,OP,Reg1,Reg2);
// endmodule

// module RegTest();
//     reg [4:0] read1,read2,write;
//     reg [31:0] writeData;
//     wire [31:0] readdata1,readdata2;
//     reg write_enable;
//     reg clk;
//         initial
//             begin
//                 clk=0;
//                 $monitor("Reg1= %d Reg2=%d write = %d",readdata1,readdata2,writeData);
//                 #0 //Addition  Result 13
//                 read1 <=1;
//                 read2 <=2;
//                 write <= 3;
//                 writeData <= 1000;
//                 write_enable <=1;
//             end
//     Register myreg(read1,read2,write,writeData,readdata1,readdata2,write_enable,clk);
//         always begin
//             #5 clk=~clk;
//         end
// endmodule


// module finalTest();

// reg [4:0] read1,read2,write;
// reg mux_ctrl,write_enable;
// reg [4:0]shift_amount;
// reg [3:0] op;
// reg signed [31:0] external_data;
// wire signed [31:0] result;
// reg clk;
// wire [31:0] writeregdata;
//     initial begin
//         clk=0;
//         $monitor("ReadReg1 = %d / ReadReg2= %d / writeReg = %d / mux_ctrl = %d / write enabled = %d /shift_amount = %d /op = %b /Result = %d\n"
//         ,read1,read2,write,mux_ctrl,write_enable,shift_amount,op,result);
        
//         #0
//         read1 <= 10;
//         read2 <= 20;
//         write <= 3;
//         external_data <= 1000;
//         mux_ctrl <= 0;
//         write_enable <= 0;
//         shift_amount <= 3;
//         op <= 4'b0001;
//         $display("adding Register 10 with Reg 20 Result = 30");
//         #10
//         read1 <= 10;
//         read2 <= 20;
//         write <= 3;
//         external_data <= 1000;
//         mux_ctrl <= 0;
//         write_enable <= 0;
//         shift_amount <= 3;
//         op <= 4'b0010;
//         $display("subtracting Register 10 with Reg 20 Result = -10");
//         #20
//         read1 <= 1;
//         read2 <= 3;
//         write <= 3;
//         external_data <= 1000;
//         mux_ctrl <= 0;
//         write_enable <= 0;
//         shift_amount <= 3;
//         op <= 4'b0011;
//         $display("ANDing Register 1 with Reg 3 Result = 1");
//         #30
//         read1 <= 0;
//         read2 <= 3;
//         write <= 3;
//         external_data <= 1000;
//         mux_ctrl <= 0;
//         write_enable <= 0;
//         shift_amount <= 3;
//         op <= 4'b0100;
//         $display("ORing Register 0 with Reg 3 Result = 3");
//         #40
//         read1 <= 10;
//         read2 <= 20;
//         write <= 3;
//         external_data <= 1000;
//         mux_ctrl <= 0;
//         write_enable <= 0;
//         shift_amount <= 3;
//         op <= 4'b0101;
//         $display("Shift Left register(10) with shift_amount 3 = 80");
//         #50
//         read1 <= 28;
//         read2 <= 20;
//         write <= 3;
//         external_data <= 1000;
//         mux_ctrl <= 0;
//         write_enable <= 0;
//         shift_amount <= 2;
//         op <= 4'b0110;
//         $display("Shift Right logical register(28) with shift_amount 2 = 7");
//         #60
//         read1 <= 10;
//         read2 <= 20;
//         write <= 3;
//         external_data <= 1000;
//         mux_ctrl <= 0;
//         write_enable <= 0;
//         shift_amount <= 3;
//         op <= 4'b1000;
//         $display("Greater Than test register(10) with Register(20) Result= false(0)");
//         #70
//         read1 <= 10;
//         read2 <= 20;
//         write <= 3;
//         external_data <= 1000;
//         mux_ctrl <= 0;
//         write_enable <= 0;
//         shift_amount <= 3;
//         op <= 4'b1001;
//         $display("Less Than test register(10) with Register(20) Result= true(1)");
//         end
//     wholecircuit mycircuit(read1,read2,write,external_data,mux_ctrl,write_enable,shift_amount,op,clk,result);
//         always begin
//             #5 clk=~clk;
//         end
// endmodule