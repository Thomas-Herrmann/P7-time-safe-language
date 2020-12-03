//This file was generated from (Commercial) UPPAAL 4.0.15 rev. CB6BB307F6F681CB, November 2019

/*

*/
A<> (pSen1 imply pLig1)

/*

*/
A<> pLig1

/*

*/
E<> (P_Temp0.Terminated)

/*

*/
A[] ((pLig1 imply (not pLig2)) and (pLig2 imply (not pLig1)))

/*

*/
(P_Temp0.parInit5973 and pSen2 and pLig1)  --> pLig2

/*

*/
A[] (not deadlock)
