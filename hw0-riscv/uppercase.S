        .section .data
input_string:   .asciz "wow!(#@)@#absdsadbsadbsadb"

        # tohost/fromhost are data locations used by Spike
        .align 8
tohost: .byte 0
        .align 8
fromhost: .byte 0

        .section .text
        .globl _start
_start:
        la a0, input_string    # Loading input string
        
        # Bounds for whether to upper case or not
        # [97, 122] and shift up by 32
        
        li t0, 97              # Left bound
        li t1, 122             # Right bound
        li t2, 32              # offset
loop:
        # Load the current character into a1
        lb a1, 0(a0)           

        # Check if Null -> jump to end of program
        beqz a1, end_program   

        # Check if the character is lowercase 
        blt a1, t0, skip       
        bgt a1, t1, skip       

        # Convert the character to uppercase
        sub a1, a1, t2         # shift
        sb a1, 0(a0)           # update

skip:
        addi a0, a0, 1         
        j loop                 

end_program:
        j end_program