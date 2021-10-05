#define MAX_BRANCHES 8
#define ROT(x , n) ((( x) >> (n )) | (( x) << (32 - (n))) )
#define ELL(x) ( ROT ((( x ) ^ (( x ) << 16) ) , 16) )

// Round constants
static const uint32_t RCON1 [ MAX_BRANCHES ] = {
	0xB7E15162 , 0xBF715880 , 0x38B4DA56 , 0x324E7738 ,
	0xBB1185EB , 0x4F7C7B57 , 0xCFBFA1C8 , 0xC2B3293D};



void sparkle_modified1 ( uint32_t * state , int nb , int ns )
{

 int i; // Step and branch counter
 uint32_t tmpx , tmpy , x0 , y0 ;

 for (i = 0; i < ns ; i ++) {

	Hacl_Impl_Sparkle_add2(nb, i, state);
	Hacl_Impl_Sparkle_arx_n(nb, state);
	Hacl_Impl_Sparkle_l(nb, state); 
	
	state[2] = state[8];
	state[3] = state[9];
	state[0] = state[10];
	state[1] = state[11];

}



}