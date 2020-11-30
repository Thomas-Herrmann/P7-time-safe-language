//This file was generated from (Commercial) UPPAAL 4.0.15 rev. CB6BB307F6F681CB, November 2019

/*

*/
E<> pLig2

/*

*/
E<> pLig1

/*

*/
A[] ((pLig1 imply (not pLig2)) and (pLig2 imply (not pLig1)))

/*

*/
A[] (not deadlock)
