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


	uint32_t tx = (uint32_t)0U;
  	uint32_t ty = (uint32_t)0U;


  	Hacl_Impl_Sparkle_xor(nb, state, &tx, &ty);
	tmpx = (tx << (uint32_t)16U | tx >> (uint32_t)16U) ^ (tx & (uint32_t)0xffffU);
	tmpy = (ty << (uint32_t)16U | ty >> (uint32_t)16U) ^ (ty & (uint32_t)0xffffU);
	Hacl_Impl_Sparkle_xor_x(nb, state, tmpy, tmpx);



	// uint32_t tx = (uint32_t)0U;
	// uint32_t ty = (uint32_t)0U;
	// Hacl_Impl_Sparkle_xor(n, b, &tx, &ty);
	// uint32_t uu____0 = tx;
	// uint32_t
	// 	ltx = (uu____0 << (uint32_t)16U | uu____0 >> (uint32_t)16U) ^ (uu____0 & (uint32_t)0xffffU);
	
	// uint32_t uu____1 = ty;
	// uint32_t
	//   lty = (uu____1 << (uint32_t)16U | uu____1 >> (uint32_t)16U) ^ (uu____1 & (uint32_t)0xffffU);
	// Hacl_Impl_Sparkle_xor_x(n, b, lty, ltx);



  	x0 = state [0];
	y0 = state [1];



	// // does not influence
	// state [0] = state [0] ^ tmpy;
	// state [2] = state [2] ^ tmpy;

	// // does not influence
	// state[1] = state[1] ^ tmpx;
	// state[3] = state[3] ^ tmpx;


	state [0] = state [6] ^ state [2];
	state [6] = state [2] ^ tmpy;
	state [1] = state [7] ^ state [3] ;
	state [7] = state [3] ^ tmpx ;

	
	// state [2] = state [8] ^ state [4] ^ tmpy ;
	// state [2] = state [4];
	// state [8] = state [4];
	// state [3] = state [9] ^ state [5] ^ tmpx ;
	// state [3] = state [5] ^ tmpx;
	// state [9] = state [5];

	state [2] = state [4] ^ x0;
	state [4] = x0 ^ tmpy;
	state [3] = state [5] ^ y0;
	state [5] = y0 ^ tmpx; 
}



}