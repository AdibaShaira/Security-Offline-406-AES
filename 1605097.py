import codecs
import time
import base64 
from BitVector import *
from itertools import islice
Sbox = (
    0x63, 0x7C, 0x77, 0x7B, 0xF2, 0x6B, 0x6F, 0xC5, 0x30, 0x01, 0x67, 0x2B, 0xFE, 0xD7, 0xAB, 0x76,
    0xCA, 0x82, 0xC9, 0x7D, 0xFA, 0x59, 0x47, 0xF0, 0xAD, 0xD4, 0xA2, 0xAF, 0x9C, 0xA4, 0x72, 0xC0,
    0xB7, 0xFD, 0x93, 0x26, 0x36, 0x3F, 0xF7, 0xCC, 0x34, 0xA5, 0xE5, 0xF1, 0x71, 0xD8, 0x31, 0x15,
    0x04, 0xC7, 0x23, 0xC3, 0x18, 0x96, 0x05, 0x9A, 0x07, 0x12, 0x80, 0xE2, 0xEB, 0x27, 0xB2, 0x75,
    0x09, 0x83, 0x2C, 0x1A, 0x1B, 0x6E, 0x5A, 0xA0, 0x52, 0x3B, 0xD6, 0xB3, 0x29, 0xE3, 0x2F, 0x84,
    0x53, 0xD1, 0x00, 0xED, 0x20, 0xFC, 0xB1, 0x5B, 0x6A, 0xCB, 0xBE, 0x39, 0x4A, 0x4C, 0x58, 0xCF,
    0xD0, 0xEF, 0xAA, 0xFB, 0x43, 0x4D, 0x33, 0x85, 0x45, 0xF9, 0x02, 0x7F, 0x50, 0x3C, 0x9F, 0xA8,
    0x51, 0xA3, 0x40, 0x8F, 0x92, 0x9D, 0x38, 0xF5, 0xBC, 0xB6, 0xDA, 0x21, 0x10, 0xFF, 0xF3, 0xD2,
    0xCD, 0x0C, 0x13, 0xEC, 0x5F, 0x97, 0x44, 0x17, 0xC4, 0xA7, 0x7E, 0x3D, 0x64, 0x5D, 0x19, 0x73,
    0x60, 0x81, 0x4F, 0xDC, 0x22, 0x2A, 0x90, 0x88, 0x46, 0xEE, 0xB8, 0x14, 0xDE, 0x5E, 0x0B, 0xDB,
    0xE0, 0x32, 0x3A, 0x0A, 0x49, 0x06, 0x24, 0x5C, 0xC2, 0xD3, 0xAC, 0x62, 0x91, 0x95, 0xE4, 0x79,
    0xE7, 0xC8, 0x37, 0x6D, 0x8D, 0xD5, 0x4E, 0xA9, 0x6C, 0x56, 0xF4, 0xEA, 0x65, 0x7A, 0xAE, 0x08,
    0xBA, 0x78, 0x25, 0x2E, 0x1C, 0xA6, 0xB4, 0xC6, 0xE8, 0xDD, 0x74, 0x1F, 0x4B, 0xBD, 0x8B, 0x8A,
    0x70, 0x3E, 0xB5, 0x66, 0x48, 0x03, 0xF6, 0x0E, 0x61, 0x35, 0x57, 0xB9, 0x86, 0xC1, 0x1D, 0x9E,
    0xE1, 0xF8, 0x98, 0x11, 0x69, 0xD9, 0x8E, 0x94, 0x9B, 0x1E, 0x87, 0xE9, 0xCE, 0x55, 0x28, 0xDF,
    0x8C, 0xA1, 0x89, 0x0D, 0xBF, 0xE6, 0x42, 0x68, 0x41, 0x99, 0x2D, 0x0F, 0xB0, 0x54, 0xBB, 0x16,
)
InvSbox = (
    0x52, 0x09, 0x6A, 0xD5, 0x30, 0x36, 0xA5, 0x38, 0xBF, 0x40, 0xA3, 0x9E, 0x81, 0xF3, 0xD7, 0xFB,
    0x7C, 0xE3, 0x39, 0x82, 0x9B, 0x2F, 0xFF, 0x87, 0x34, 0x8E, 0x43, 0x44, 0xC4, 0xDE, 0xE9, 0xCB,
    0x54, 0x7B, 0x94, 0x32, 0xA6, 0xC2, 0x23, 0x3D, 0xEE, 0x4C, 0x95, 0x0B, 0x42, 0xFA, 0xC3, 0x4E,
    0x08, 0x2E, 0xA1, 0x66, 0x28, 0xD9, 0x24, 0xB2, 0x76, 0x5B, 0xA2, 0x49, 0x6D, 0x8B, 0xD1, 0x25,
    0x72, 0xF8, 0xF6, 0x64, 0x86, 0x68, 0x98, 0x16, 0xD4, 0xA4, 0x5C, 0xCC, 0x5D, 0x65, 0xB6, 0x92,
    0x6C, 0x70, 0x48, 0x50, 0xFD, 0xED, 0xB9, 0xDA, 0x5E, 0x15, 0x46, 0x57, 0xA7, 0x8D, 0x9D, 0x84,
    0x90, 0xD8, 0xAB, 0x00, 0x8C, 0xBC, 0xD3, 0x0A, 0xF7, 0xE4, 0x58, 0x05, 0xB8, 0xB3, 0x45, 0x06,
    0xD0, 0x2C, 0x1E, 0x8F, 0xCA, 0x3F, 0x0F, 0x02, 0xC1, 0xAF, 0xBD, 0x03, 0x01, 0x13, 0x8A, 0x6B,
    0x3A, 0x91, 0x11, 0x41, 0x4F, 0x67, 0xDC, 0xEA, 0x97, 0xF2, 0xCF, 0xCE, 0xF0, 0xB4, 0xE6, 0x73,
    0x96, 0xAC, 0x74, 0x22, 0xE7, 0xAD, 0x35, 0x85, 0xE2, 0xF9, 0x37, 0xE8, 0x1C, 0x75, 0xDF, 0x6E,
    0x47, 0xF1, 0x1A, 0x71, 0x1D, 0x29, 0xC5, 0x89, 0x6F, 0xB7, 0x62, 0x0E, 0xAA, 0x18, 0xBE, 0x1B,
    0xFC, 0x56, 0x3E, 0x4B, 0xC6, 0xD2, 0x79, 0x20, 0x9A, 0xDB, 0xC0, 0xFE, 0x78, 0xCD, 0x5A, 0xF4,
    0x1F, 0xDD, 0xA8, 0x33, 0x88, 0x07, 0xC7, 0x31, 0xB1, 0x12, 0x10, 0x59, 0x27, 0x80, 0xEC, 0x5F,
    0x60, 0x51, 0x7F, 0xA9, 0x19, 0xB5, 0x4A, 0x0D, 0x2D, 0xE5, 0x7A, 0x9F, 0x93, 0xC9, 0x9C, 0xEF,
    0xA0, 0xE0, 0x3B, 0x4D, 0xAE, 0x2A, 0xF5, 0xB0, 0xC8, 0xEB, 0xBB, 0x3C, 0x83, 0x53, 0x99, 0x61,
    0x17, 0x2B, 0x04, 0x7E, 0xBA, 0x77, 0xD6, 0x26, 0xE1, 0x69, 0x14, 0x63, 0x55, 0x21, 0x0C, 0x7D,
)
Mixer = [
    [BitVector(hexstring="02"), BitVector(hexstring="03"), BitVector(hexstring="01"), BitVector(hexstring="01")],
    [BitVector(hexstring="01"), BitVector(hexstring="02"), BitVector(hexstring="03"), BitVector(hexstring="01")],
    [BitVector(hexstring="01"), BitVector(hexstring="01"), BitVector(hexstring="02"), BitVector(hexstring="03")],
    [BitVector(hexstring="03"), BitVector(hexstring="01"), BitVector(hexstring="01"), BitVector(hexstring="02")]
]
InvMixer = [
    [BitVector(hexstring="0E"), BitVector(hexstring="0B"), BitVector(hexstring="0D"), BitVector(hexstring="09")],
    [BitVector(hexstring="09"), BitVector(hexstring="0E"), BitVector(hexstring="0B"), BitVector(hexstring="0D")],
    [BitVector(hexstring="0D"), BitVector(hexstring="09"), BitVector(hexstring="0E"), BitVector(hexstring="0B")],
    [BitVector(hexstring="0B"), BitVector(hexstring="0D"), BitVector(hexstring="09"), BitVector(hexstring="0E")]
]

def subBoxvalue(b):
    #print(b)
    if(b.intValue()==0):
        bv=BitVector(hexstring="63")
        return bv
    AES_modulus = BitVector(bitstring='100011011')
    bv3 = b.gf_MI(AES_modulus, 8)
    var = BitVector(hexstring="63")
    b1=var ^ bv3 ^ (bv3<<1) ^ (bv3<<1) ^ (bv3<<1) ^(bv3<<1) 
    a=b1.get_bitvector_in_hex()
    #print(a)
    return b1
def invSubBoxValue(b):
     bh=b.intValue()
     #print("------bh------",bh)
     if(bh==99):
        bv=BitVector(hexstring="0")
        return bv
     var=BitVector(hexstring="5")
     b1= var ^ (b<<1) ^ (b<<2) ^ (b<<3)
     AES_modulus = BitVector(bitstring='100011011')
     bv3 = b1.gf_MI(AES_modulus, 8)
     #print("--------bv3-----", bv3)
     a=bv3.get_bitvector_in_hex()
     #print(a)
     return bv3
def g_function_rotate(w):
    w_temp=[w[1],w[2],w[3],w[0]]
   # for ch in  w_temp:
        #print(ch.get_bitvector_in_hex())
    
    return w_temp
def subbox(w):
    w_sub=[]
    for x in w:
       # b = BitVector(hexstring=x.get_bitvector_in_hex())
        #int_val = b.intValue()
        #s = Sbox[int_val]
        #s = BitVector(intVal=s, size=8)
        #print(s.get_bitvector_in_hex())
        s=subBoxvalue(x)
        #print("------sub------")
        #print(s)
        w_sub.append(s)
    #for ch in  w_sub:
        #print(ch.get_bitvector_in_hex())
    return w_sub
    
hex_array_key=[]
bit_array_key=[]
val = input("Enter your key: ") 
print("Key:")
print(val)
for ch in val:
      h=format(ord(ch), "x")
      b = BitVector(hexstring=h)
      int_val = b.intValue()
      s = BitVector(intVal=int_val, size=8)
      hex_array_key.append(h)
      bit_array_key.append(s)
#print(hex_array_key) 
start_time = time.time()
round_zero_key = [[] for j in range(4)]
for row in range(4):
     for coloumn in range(4):
        round_zero_key[row].append(bit_array_key[row + 4 * coloumn])
#print(round_zero_key)
w0=[round_zero_key[0][0],round_zero_key[1][0],round_zero_key[2][0],round_zero_key[3][0]]
w1=[round_zero_key[0][1],round_zero_key[1][1],round_zero_key[2][1],round_zero_key[3][1]]
w2=[round_zero_key[0][2],round_zero_key[1][2],round_zero_key[2][2],round_zero_key[3][2]]
w3=[round_zero_key[0][3],round_zero_key[1][3],round_zero_key[2][3],round_zero_key[3][3]]
'''
for ch in  w0:
    print(ch.get_bitvector_in_hex())
print("w1")
for ch in  w1:
    print(ch.get_bitvector_in_hex())
print("w2")
for ch in  w2:
     print(ch.get_bitvector_in_hex())
print("w3")
for ch in  w3:
     print(ch.get_bitvector_in_hex())
'''
def bittohex(w):
    print_w=[]
    for ch in  w:
         a=ch.get_bitvector_in_hex()
         print_w.append(a)
    return print_w

def print_bit_vector(w):
    print_w=[]
    for ch in  w:
         a=ch.get_bitvector_in_hex()
         print_w.append(a)
    #print(print_w)
    return print_w
def xor_bit_vector(w1,w2):
    result=[]
    for ch in  range(4):
         result_bv  =  w1[ch] ^ w2[ch]
         result.append(result_bv)
    return result
def keygen(w0,w1,w2,w3):
     key1=[]
     key1.extend(w0)
     key1.extend(w1)
     key1.extend(w2)
     key1.extend(w3)
     return key1
w_temp=[]
w_temp=g_function_rotate(w3)
w_sub=[]
w_sub=subbox(w_temp)
w_sub_hex=print_bit_vector(w_sub)
w_sub_int=[int(x, 16) for x in w_sub_hex]
round_const_bit=[1,00,00,00]
#xor_bit_vector(round_const_bit,w_sub)
def hextoint(w):
    w_sub_int=[int(x, 16) for x in w]
    return w_sub_int

def inttohex(result):
     result_xor_hex=[]
     for item in result:
        h=format((item), "x")
        result_xor_hex.append(h)
     return result_xor_hex
     #print(result_xor_hex)
def hextobit(w):
    bit_array=[]
    for h in w:
        b = BitVector(hexstring=h)
        int_val = b.intValue()
        s = BitVector(intVal=int_val, size=8)
        bit_array.append(s)
    return bit_array
def nextRound(rc):
    result=[]
    AES_modulus = BitVector(bitstring='100011011')
    for i in rc:
      bv1 = BitVector(hexstring="02")
      bv2 = BitVector(hexstring=i)
      bv3 = bv1.gf_multiply_modular(bv2, AES_modulus, 8)
      result.append(bv3)
    return result
result=[round_const_bit[0] ^ w_sub_int[0],round_const_bit[1] ^ w_sub_int[1],round_const_bit[2] ^ w_sub_int[2],round_const_bit[3] ^ w_sub_int[3]]
result_hex_m=inttohex(result)
result_g3=hextobit(result_hex_m)
w4=xor_bit_vector(w0,result_g3)
#print_bit_vector(w4)
w5=xor_bit_vector(w4,w1)
#print_bit_vector(w5)
w6=xor_bit_vector(w5,w2)
#print_bit_vector(w6)
w7=xor_bit_vector(w6,w3)
#print_bit_vector(w7)
key0=keygen(w0,w1,w2,w3)
#print_bit_vector(key0)
key1=keygen(w4,w5,w6,w7)
#print_bit_vector(key1)
round_2nd_hex=inttohex(round_const_bit)
round_2nd_bit=hextobit(round_2nd_hex)
#round_2nd_bit=hextobit(round_2nd_hex)
round_2nd_rc=nextRound(round_2nd_hex)
#print_bit_vector(round_2nd_rc)
key_gen_array=[w0,w1,w2,w3,w4,w5,w6,w7]
key_pringt_array=[bittohex(w0),bittohex(w1),bittohex(w2),bittohex(w3),bittohex(w4),bittohex(w5),bittohex(w6),bittohex(w7)]
#print(key_pringt_array)
def round_constant_gen(rc):
    round_2nd_hex=bittohex(rc)
    round_2nd_rc=nextRound(round_2nd_hex)
    #print("rounc constant")
    #print_bit_vector(round_2nd_rc)
    return round_2nd_rc
def key_expansion(rc):
    round_2nd_rc=rc
    for row in range(8,44):
        if(row%4==0):
           w_temp=g_function_rotate(key_gen_array[row-1])
           #print_bit_vector(w_temp)
           w_sub=subbox(w_temp)
           w_sub_hex=print_bit_vector(w_sub)
           round_2nd_rc=round_constant_gen(round_2nd_rc)
           w_var=xor_bit_vector(round_2nd_rc,w_sub)
           #print(bittohex(w_var))
           w_var=xor_bit_vector(key_gen_array[row-4],w_var)
           key_gen_array.append(w_var)
           #print("-------loop er % 0------")
           #print(bittohex(w_var))
           key_pringt_array.append(bittohex(w_var))
        else:
           w_var=xor_bit_vector(key_gen_array[row-1],key_gen_array[row-4])
           key_gen_array.append(w_var)
           #print("-------loop er normal---")
           #print(bittohex(w_var))
           key_pringt_array.append(bittohex(w_var))
    #print(key_pringt_array)

key_expansion(round_2nd_bit)
#2d er jonne print
def keyprint(k):
   for i in range(4):
      bittohex(k[i])

          
          
 
key2=keygen(key_gen_array[8],key_gen_array[9],key_gen_array[10],key_gen_array[11])
#print_bit_vector(key2)
key3=keygen(key_gen_array[12],key_gen_array[13],key_gen_array[14],key_gen_array[15])
#print_bit_vector(key3)
key4=keygen(key_gen_array[16],key_gen_array[17],key_gen_array[18],key_gen_array[19])
#print_bit_vector(key4)
key5=keygen(key_gen_array[20],key_gen_array[21],key_gen_array[22],key_gen_array[23])
#print_bit_vector(key5)
key6=keygen(key_gen_array[24],key_gen_array[25],key_gen_array[26],key_gen_array[27])
#print_bit_vector(key6)
key7=keygen(key_gen_array[28],key_gen_array[29],key_gen_array[30],key_gen_array[31])
#print_bit_vector(key7)
key8=keygen(key_gen_array[32],key_gen_array[33],key_gen_array[34],key_gen_array[35])
#print_bit_vector(key8)
key9=keygen(key_gen_array[36],key_gen_array[37],key_gen_array[38],key_gen_array[39])
#print("---------Key9---------")
#print_bit_vector(key9)
key10=keygen(key_gen_array[40],key_gen_array[41],key_gen_array[42],key_gen_array[43])
#print_bit_vector(key10)
keys=[key0,key1,key2,key3,key4,key5,key6,key7,key8,key9,key10]
print("Key Scheduling--- %s seconds ---" % (time.time() - start_time))
def trasnferto2d(w):
   dmat = [[] for j in range(4)]
   for row in range(4):
      for coloumn in range(4):
         dmat[row].append(w[row + 4 * coloumn])
   return dmat
def round0(bit_array,key0):
    key0_2d=trasnferto2d(key0)
    #for i in range(4):
      #print(bittohex(key0_2d[i]))
    state_mat=trasnferto2d(bit_array)
    #for i in range(4):
          #print(bittohex(state_mat[i]))
    rows, cols = (4, 4) 
    arr = [[0]*cols]*rows 
    arr_hex=[]
    for i in range(4):
        for j in range(4):
            arr[i][j]=state_mat[i][j]^key0_2d[i][j]
            arr_hex.append(arr[i][j])
       
    #print(bittohex(arr_hex))
    dmat=[[arr_hex[0],arr_hex[1],arr_hex[2],arr_hex[3]],
          [arr_hex[4],arr_hex[5],arr_hex[6],arr_hex[7]],  
           [arr_hex[8],arr_hex[9],arr_hex[10],arr_hex[11]],
            [arr_hex[12],arr_hex[13],arr_hex[14],arr_hex[15]]  ]
    #for i in range(4):
          #print(bittohex(dmat[i]))
    return dmat
def subBytes(state):
    #print("----SubBytes------")
    arr_hex=[]
    for r in range(4):
        w=subbox((state[r]))
        w_sub_hex=print_bit_vector(w)
        arr_hex.extend(w)
    #print(bittohex(w2))
    dmat=[[arr_hex[0],arr_hex[1],arr_hex[2],arr_hex[3]],
          [arr_hex[4],arr_hex[5],arr_hex[6],arr_hex[7]],  
           [arr_hex[8],arr_hex[9],arr_hex[10],arr_hex[11]],
            [arr_hex[12],arr_hex[13],arr_hex[14],arr_hex[15]]  ]
    #for i in range(4):
          #print(bittohex(dmat[i]))
    return dmat
    
def leftshift_2(w):
     w_temp=[w[2],w[3],w[0],w[1]]
     return w_temp
def leftshift_3(w):
     w_temp=[w[3],w[0],w[1],w[2]]
     return w_temp

def row_shift(state):
    #print("-----Row_Shift------")
    arr_hex=[]
    arr_hex.extend(state[0])
    arr_hex.extend(g_function_rotate(state[1]))
    arr_hex.extend(leftshift_2(state[2]))
    arr_hex.extend(leftshift_3(state[3]))
    #print(bittohex(w2))
    dmat=[[arr_hex[0],arr_hex[1],arr_hex[2],arr_hex[3]],
          [arr_hex[4],arr_hex[5],arr_hex[6],arr_hex[7]],  
           [arr_hex[8],arr_hex[9],arr_hex[10],arr_hex[11]],
            [arr_hex[12],arr_hex[13],arr_hex[14],arr_hex[15]]  ]
    #for i in range(4):
          #print(bittohex(dmat[i]))
    return dmat
def mix_coloumns(state):
    #print("----mixcoloumns---")
    AES_modulus = BitVector(bitstring='100011011')
    rows, cols = (4, 4) 
    arr = [[0]*cols]*rows 
    arr=[hextobit(inttohex(arr[0])),hextobit(inttohex(arr[1])),hextobit(inttohex(arr[2])),hextobit(inttohex(arr[3]))]
    #print(arr)
    arr_hex=[]
    for i in range(4):
        for j in range(4):
            for k in range(4):
                a=Mixer[i][k]
                #print("i and k ",i,k)
                #print(format((a.intValue()),"x"))
                b=state[k][j]
                #print("k and j ",k,j)
                #print(format((b.intValue()),"x"))
                bv3=a.gf_multiply_modular(b,AES_modulus,8)
                arr[i][j]=arr[i][j] ^ bv3
            arr_hex.append(arr[i][j])
            
    
    #arr_hex=inttohex(arr_hex)
    #print(arr_hex)
    #arr_hex=hextobit(arr_hex)
    #print(bittohex(arr_hex))
    dmat=[[arr_hex[0],arr_hex[1],arr_hex[2],arr_hex[3]],
          [arr_hex[4],arr_hex[5],arr_hex[6],arr_hex[7]],  
           [arr_hex[8],arr_hex[9],arr_hex[10],arr_hex[11]],
            [arr_hex[12],arr_hex[13],arr_hex[14],arr_hex[15]]  ]
    #for i in range(4):
          #print(bittohex(dmat[i]))
          
    return dmat
def roundKeyadd(state_mat,rc):
    key0_2d=trasnferto2d(rc)
    rows, cols = (4, 4) 
    arr = [[0]*cols]*rows 
    arr_hex=[]
    for i in range(4):
        for j in range(4):
            arr[i][j]=state_mat[i][j]^key0_2d[i][j]
            arr_hex.append(arr[i][j])
       
    #print(bittohex(arr_hex))
    dmat=[[arr_hex[0],arr_hex[1],arr_hex[2],arr_hex[3]],
          [arr_hex[4],arr_hex[5],arr_hex[6],arr_hex[7]],  
           [arr_hex[8],arr_hex[9],arr_hex[10],arr_hex[11]],
            [arr_hex[12],arr_hex[13],arr_hex[14],arr_hex[15]]  ]
    #for i in range(4):
          #print(bittohex(dmat[i]))
    return dmat
def otherrounds(state,key):
    rows, cols = (4, 4) 
    final_state = [[0]*cols]*rows 
    state_sub=subBytes(state)
    state_rs=row_shift(state_sub)
    state_mix_c=mix_coloumns(state_rs)
    final_state=roundKeyadd(state_mix_c,key)
    #print("----final state----")
    #for i in range(4):
          #print(bittohex(final_state[i]))
    #print("----final state----")
    return final_state




def final_round(state,key):
    rows, cols = (4, 4) 
    final_state = [[0]*cols]*rows 
    state_sub=subBytes(state)
    state_rs=row_shift(state_sub)
    final_state=roundKeyadd(state_rs,key)
    #print("----final state----")
    #for i in range(4):
          #print(bittohex(final_state[i]))
    #print("----final state----")
    return final_state
 

def decryption(state):
  def addRoundkey(state,key):
    key0_2d=trasnferto2d(key)
    rows, cols = (4, 4) 
    arr = [[0]*cols]*rows 
    arr_hex=[]
    for i in range(4):
        for j in range(4):
            arr[i][j]=state[i][j]^key0_2d[i][j]
            arr_hex.append(arr[i][j])
       
    #print(bittohex(arr_hex))
    dmat=[[arr_hex[0],arr_hex[1],arr_hex[2],arr_hex[3]],
          [arr_hex[4],arr_hex[5],arr_hex[6],arr_hex[7]],  
           [arr_hex[8],arr_hex[9],arr_hex[10],arr_hex[11]],
            [arr_hex[12],arr_hex[13],arr_hex[14],arr_hex[15]]  ]
    #for i in range(4):
          #print(bittohex(dmat[i]))
    return dmat
  def righshtit1(w):
        w_temp=[w[3],w[0],w[1],w[2]]  
        return w_temp
  def righshtit2(w):
        w_temp=[w[2],w[3],w[0],w[1]]  
        return w_temp
  def righshtit3(w):
        w_temp=[w[1],w[2],w[3],w[0]]  
        return w_temp
  def inverse_row_shift(state):
        #print("-----Row_Shift------")
        arr_hex=[]
        arr_hex.extend(state[0])
        arr_hex.extend(righshtit1(state[1]))
        arr_hex.extend(righshtit2(state[2]))
        arr_hex.extend(righshtit3(state[3]))
        #print(bittohex(w2))
        dmat=[[arr_hex[0],arr_hex[1],arr_hex[2],arr_hex[3]],
            [arr_hex[4],arr_hex[5],arr_hex[6],arr_hex[7]],  
            [arr_hex[8],arr_hex[9],arr_hex[10],arr_hex[11]],
            [arr_hex[12],arr_hex[13],arr_hex[14],arr_hex[15]]  ]
        #for i in range(4):
          #print(bittohex(dmat[i]))
        return dmat
  def invsubbox(w):
        #print("----invsubbox----")
        w_sub=[]
        for x in w:
            #b = BitVector(hexstring=x.get_bitvector_in_hex())
            #int_val = b.intValue()
            #s = InvSbox[int_val]
            #s = BitVector(intVal=s, size=8)
            s=invSubBoxValue(x)
            w_sub.append(s)
    
        return w_sub
  def invsubBytes(state):
        #print("---invsubbytes---")
        arr_hex=[]
        for r in range(4):
           w=invsubbox((state[r]))
           w_sub_hex=print_bit_vector(w)
           arr_hex.extend(w)
    #print(bittohex(w2))
        dmat=[[arr_hex[0],arr_hex[1],arr_hex[2],arr_hex[3]],
          [arr_hex[4],arr_hex[5],arr_hex[6],arr_hex[7]],  
           [arr_hex[8],arr_hex[9],arr_hex[10],arr_hex[11]],
            [arr_hex[12],arr_hex[13],arr_hex[14],arr_hex[15]]  ]
        #for i in range(4):
          #print(bittohex(dmat[i]))
        return dmat
  def invMixcolumns(state):
        #print("----mixcoloumns---")
        AES_modulus = BitVector(bitstring='100011011')
        rows, cols = (4, 4) 
        arr = [[0]*cols]*rows 
        arr=[hextobit(inttohex(arr[0])),hextobit(inttohex(arr[1])),hextobit(inttohex(arr[2])),hextobit(inttohex(arr[3]))]
        #print(arr)
        arr_hex=[]
        for i in range(4):
           for j in range(4):
              for k in range(4):
                a=InvMixer[i][k]
                b=state[k][j]
                bv3=a.gf_multiply_modular(b,AES_modulus,8)
                arr[i][j]=arr[i][j] ^ bv3
              arr_hex.append(arr[i][j])   
        #print(bittohex(arr_hex))
        dmat=[[arr_hex[0],arr_hex[1],arr_hex[2],arr_hex[3]],
          [arr_hex[4],arr_hex[5],arr_hex[6],arr_hex[7]],  
           [arr_hex[8],arr_hex[9],arr_hex[10],arr_hex[11]],
            [arr_hex[12],arr_hex[13],arr_hex[14],arr_hex[15]]  ]
        #for i in range(4):
            #print(bittohex(dmat[i]))
          
        return dmat
        
  state_round_0=addRoundkey(state,key10)
  state_round_0=inverse_row_shift(state_round_0)
  state_round_0=invsubBytes(state_round_0)
  state_round_0=addRoundkey(state_round_0,key9)
  state_round_0=invMixcolumns(state_round_0)
  for i in range(2,10):
      #print("-----round no----",i)
      state_round_0=inverse_row_shift(state_round_0)
      state_round_0=invsubBytes(state_round_0)
      state_round_0=addRoundkey(state_round_0,keys[10-i])
      state_round_0=invMixcolumns(state_round_0)
  
  state_round_0=inverse_row_shift(state_round_0)
  state_round_0=invsubBytes(state_round_0)
  state_round_0=addRoundkey(state_round_0,keys[0])
  return state_round_0


hex_array = []
bit_array=[]
line_array=[]
f = open("Demofile.txt","r")
#while next_line != "":
#   text=f.read(16)
#   print(text)
#   next_line = f.readline()
for line in f:
    for character in line:
        h=format(ord(character), "x")
        #print(h)
        b = BitVector(hexstring=h)
        int_val = b.intValue()
       # b = BitVector(intVal=character)
       # int_val = character.intValue()
        s = BitVector(intVal=int_val, size=8)
        bit_array.append(s)
        hex_array.append(h)

if(len(hex_array)<16):
    while len(hex_array)<16:
        hex_array.append(" ")
        h=format(ord(" "), "x")
        b = BitVector(hexstring=h)
        int_val = b.intValue()
        s = BitVector(intVal=int_val, size=8)
        bit_array.append(s)
if(len(hex_array)>16):
     del hex_array[16:len(hex_array)]
     del bit_array[16:len(hex_array)]
#print(bit_array)
print("Plain text:")
final=[]
for ch in hex_array:
        bytes_object = bytes.fromhex(ch)
        ascii_string = bytes_object.decode("ASCII")
        final.append(ascii_string)
def convert(s): 
    
        new = "" 
    
        for x in s: 
            new += x  
        return new 
print(convert(final))
print(hex_array)
f.close()
final_text=""
encryption=[]
def start_process(bit_array):
    start_time = time.time()
    rond0=round0(bit_array,key0)
    state_1=subBytes(rond0)
    state_1_rs=row_shift(state_1)
    state_1_sc=mix_coloumns(state_1_rs)
    state_1_rca=roundKeyadd(state_1_sc,key1)
    state_f=state_1_rca
    for i in range(2,10):
       #print("---Round no----",i)
       state_f=otherrounds(state_f,keys[i])
    state_f=final_round(state_f,key10) 
    print("Encryption--- %s seconds ---" % (time.time() - start_time))
    print("Cypher text:")
    print("In hex:")
    encryption_print=[state_f[0][0],state_f[1][0],state_f[2][0],state_f[3][0],state_f[0][1],state_f[1][1],state_f[2][1],state_f[3][1],state_f[0][2],state_f[1][2],state_f[2][2],state_f[3][2],state_f[0][3],state_f[1][3],state_f[2][3],state_f[3][3]]
    print(bittohex(encryption_print))
    '''
    print("In Ascii:")
    final_en=[]
    Hex_en=bittohex(encryption_print)
    for ch in Hex_en :
        bytes_object = bytes.fromhex(ch)
        ascii_string = bytes_object.decode("ASCII")
        final_en.append(ascii_string)
    def convert(s): 
    
        new = "" 
    
        for x in s: 
            new += x  
        return new 
    print(convert(final_en))
    '''
    encryption.append(state_f)
    rows, cols = (4, 4) 
    sample_text = [[0]*cols]*rows
    start_time = time.time()
    sample_text=decryption(state_f)
    print("Decryption--- %s seconds ---" % (time.time() - start_time))
    text=[]
    text=[sample_text[0][0],sample_text[1][0],sample_text[2][0],sample_text[3][0],sample_text[0][1],sample_text[1][1],sample_text[2][1],sample_text[3][1],sample_text[0][2],sample_text[1][2],sample_text[2][2],sample_text[3][2],sample_text[0][3],sample_text[1][3],sample_text[2][3],sample_text[3][3]]
    print("Deciphered Text:")
    print("In Hex:")
    print(bittohex(text))
    text=bittohex(text)
    final=[]
    for ch in text:
        bytes_object = bytes.fromhex(ch)
        ascii_string = bytes_object.decode("ASCII")
        final.append(ascii_string)
    print(final)
    def convert(s): 
    
        new = "" 
    
        for x in s: 
            new += x  
        return new 
    final_text=convert(final)
    final_text+=final_text
    print("In text")
    print(convert(final)) 
start_process(bit_array)
def image_encryption():
    with open("sample.pdf", "rb") as image2string: 
        converted_string = base64.b64encode(image2string.read())  
    converted_string=converted_string.decode("utf-8")
        #print(converted_string)
    n = 16
    arr=[converted_string[i:i+n] for i in range(0, len(converted_string), n)]
    print(arr)
    print("------len-----",len(arr))
    j=0
    final_text=""
    for ch in range(len(arr)):
        j=j+1
        si=list(arr[ch])
        print(si)
        hex_array = []
        bit_array=[]
        for i in range(len(si)):
                h=format(ord(si[i]), "x")
                b = BitVector(hexstring=h)
                int_val = b.intValue()
                s = BitVector(intVal=int_val, size=8)
                bit_array.append(s)
                #print("bit",bit_array)
                hex_array.append(h)
        #print("-----len-----",len(bit_array))
        k=0
        if(len(hex_array)<16):
           while len(hex_array)<16:
                k=k+1
                hex_array.append(" ")
                h=format(ord(" "), "x")
                b = BitVector(hexstring=h)
                int_val = b.intValue()
                s = BitVector(intVal=int_val, size=8)
                bit_array.append(s)
        rond0=round0(bit_array,key0)
        state_1=subBytes(rond0)
        state_1_rs=row_shift(state_1)
        state_1_sc=mix_coloumns(state_1_rs)
        state_1_rca=roundKeyadd(state_1_sc,key1)
        state_f=state_1_rca
        for i in range(2,10):
            #print("---------------------Round no---------------",i)
            state_f=otherrounds(state_f,keys[i])
        state_f=final_round(state_f,key10) 
        encryption.append(state_f)
        rows, cols = (4, 4) 
        sample_text = [[0]*cols]*rows
        sample_text=decryption(state_f)
        text=[]
        text=[sample_text[0][0],sample_text[1][0],sample_text[2][0],sample_text[3][0],sample_text[0][1],sample_text[1][1],sample_text[2][1],sample_text[3][1],sample_text[0][2],sample_text[1][2],sample_text[2][2],sample_text[3][2],sample_text[0][3],sample_text[1][3],sample_text[2][3],sample_text[3][3]]
        #print(bittohex(text))
        text=bittohex(text)
        #print("-----------------------aschhriiiiiii----------------")
        final=[]
        for ch in text:
            bytes_object = bytes.fromhex(ch)
            ascii_string = bytes_object.decode("ASCII")
            final.append(ascii_string)
        if k>0:
            del final[len(s)-k:len(s)]
            print(final)
        #print(final)
        #print("-----------------------aschhriiiiiii finaaaaaaal----------------")
        def convert(s): 
            new = "" 
            for x in s: 
                new += x  
            return new 
        final_text_c=convert(final)
        print("-------------final--------------")
        final_text+=final_text_c
        #print(final_text)
        print("------------------------loop no-------------------",j)

    print(final_text)
    my_str_as_bytes = str.encode(final_text) 
    with open('encode.bin', "wb") as file: 
        file.write(my_str_as_bytes)
    file = open('encode.bin', 'rb') 
    byte = file.read() 
    file.close()   
    decodeit = open('ade.pdf', 'wb') 
    decodeit.write(base64.b64decode((byte))) 
    decodeit.close()
image_encryption()