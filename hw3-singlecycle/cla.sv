`timescale 1ns / 1ps

/**
 * @param a first 1-bit input
 * @param b second 1-bit input
 * @param g whether a and b generate a carry
 * @param p whether a and b would propagate an incoming carry
 */
module gp1(input wire a, b,
           output wire g, p);
   assign g = a & b;
   assign p = a | b;
endmodule

/**
 * Computes aggregate generate/propagate signals over a 4-bit window.
 * @param gin incoming generate signals
 * @param pin incoming propagate signals
 * @param cin the incoming carry
 * @param gout whether these 4 bits internally would generate a carry-out (independent of cin)
 * @param pout whether these 4 bits internally would propagate an incoming carry from cin
 * @param cout the carry outs for the low-order 3 bits
 */
module gp4(input wire [3:0] gin, pin,
           input wire cin,
           output wire gout, pout,
           output wire [2:0] cout);

   assign pout = pin[3] & pin[2] & pin[1] & pin[0];
   assign gout = gin[3] | (pin[3] & gin[2]) | (& pin[3:2] & gin[1]) | (& pin[3:1] & gin[0]);
   assign cout[0] = gin[0] | (pin[0] & cin);
   assign cout[1] = gin[1] | (pin[1] & gin[0]) | (& pin[1:0] & cin);
   assign cout[2] = gin[2] | (pin[2] & gin[1]) | (& pin[2:1] & gin[0]) | (& pin[2:0] & cin);
endmodule

/** Same as gp4 but for an 8-bit window instead */
module gp8(input wire [7:0] gin, pin,
           input wire cin,
           output wire gout, pout,
           output wire [6:0] cout);

   assign pout = (& pin);
   assign gout = gin[7] || (pin[7] & gin[6]) || (& pin[7:6] & gin[5]) || (& pin[7:5] & gin[4]) || (& pin[7:4] & gin[3]) || (& pin[7:3] & gin[2]) || (& pin[7:2] & gin[1]) || (& pin[7:1] & gin[0]);
   assign cout[0] = gin[0] | (pin[0] & cin);
   assign cout[1] = gin[1] | (pin[1] & gin[0]) | (&pin[1:0] & cin);
   assign cout[2] = gin[2] | (pin[2] & gin[1]) | (&pin[2:1] & gin[0]) | (&pin[2:0] & cin);
   assign cout[3] = gin[3] | (pin[3] & gin[2]) | (&pin[3:2] & gin[1]) | (&pin[3:1] & gin[0]) | (&pin[3:0] & cin);
   assign cout[4] = gin[4] | (pin[4] & gin[3]) | (&pin[4:3] & gin[2]) | (&pin[4:2] & gin[1]) | (&pin[4:1] & gin[0]) | (&pin[4:0] & cin);
   assign cout[5] = gin[5] | (pin[5] & gin[4]) | (&pin[5:4] & gin[3]) | (&pin[5:3] & gin[2]) | (&pin[5:2] & gin[1]) | (&pin[5:1] & gin[0]) | (&pin[5:0] & cin);
   assign cout[6] = gin[6] | (pin[6] & gin[5]) | (&pin[6:5] & gin[4]) | (&pin[6:4] & gin[3]) | (&pin[6:3] & gin[2]) | (&pin[6:2] & gin[1]) | (&pin[6:1] & gin[0]) | (&pin[6:0] & cin);
endmodule

module cla
  (input wire [31:0]  a, b,
   input wire         cin,
   output wire [31:0] sum);

   wire [31:0] g, p; 
   wire [31:0] int_carry; 
   wire [3:0] gout, pout; 
   wire [6:0] cout [3:0]; 
   
   genvar i;
   for (i= 0; i < 32; i= i+1) begin
      gp1 gp1_inst(
         .a(a[i]), 
         .b(b[i]), 
         .g(g[i]), 
         .p(p[i])
      );
   end

   gp8 gp8_inst0(
      .gin(g[7:0]),
      .pin(p[7:0]),
      .cin(cin),
      .gout(gout[0]),
      .pout(pout[0]),
      .cout(cout[0])
   );

   assign int_carry[8] = (gout[0]) | (pout[0] & cin);

   gp8 gp8_inst1(
      .gin(g[15:8]),
      .pin(p[15:8]),
      .cin(int_carry[8]), 
      .gout(gout[1]),
      .pout(pout[1]),
      .cout(cout[1])
   );

   assign int_carry[16] = (gout[1]) | (pout[1] & (gout[0] | (pout[0] & cin)));

   gp8 gp8_inst2(
      .gin(g[23:16]),
      .pin(p[23:16]),
      .cin(int_carry[16]),
      .gout(gout[2]),
      .pout(pout[2]),
      .cout(cout[2])
   );

   assign int_carry[24] = (gout[2]) | (pout[2] & (gout[1] | (pout[1] & (gout[0] | (pout[0] & cin)))));

   gp8 gp8_inst3(
      .gin(g[31:24]),
      .pin(p[31:24]),
      .cin(int_carry[24]),
      .gout(gout[3]),
      .pout(pout[3]),
      .cout(cout[3])
   );

   assign int_carry[0] = cin;
   assign int_carry[7:1] = cout[0];
   assign int_carry[15:9] = cout[1];
   assign int_carry[23:17] = cout[2];
   assign int_carry[31:25] = cout[3];

   assign sum = a ^ b ^ int_carry;

endmodule
