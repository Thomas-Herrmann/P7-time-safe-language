//This file was generated from (Academic) UPPAAL 4.1.24 (rev. 29A3ECA4E5FB0808), November 2019

/*

*/
pSen1 --> pLig1

/*

*/
A[] ((clkX1 > 15) and (clkX2 > 15)) imply ((not pLig1) and (not pLig2))

/*

*/
A[] (pLig1 imply (not pLig2)) and (pLig2 imply (not pLig1))

/*

*/
A[] ((Process.x > 15) and (Process2.x > 15)) imply ((Process.green1 == false) and (Process2.green2 == false))

/*

*/
pLig1 --> not pLig1

/*

*/
((not pLig1) and (not pLig2) and pSen1) --> pLig1

/*

*/
A[] not deadlock
