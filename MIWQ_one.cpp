//encoding way for the binary codes based on byte: 0 0 0 0 0 1 1 1 | 1 1 1 0 0 0 0 0 -> 224 | 7
// 


#include<cstdio>
#include<iostream>
#include<algorithm>
#include<cstring>
#include<ctime>
#include <malloc.h>
#include<map>
#include<queue>
#include<set>

#include "types.h"
#include "bitops.h"

#include "sparse_hashtable.h"
#include "bitarray.h"

using namespace std;
typedef unsigned char byte;


char sFileDir[] = "data/gist1m/lsh-e/\0";
//gist1m
const int nNumData = 1000000; // the scale of database
const int nNumQuery = 1000; // the number of the queries

//places205
//const int nNumData = 1025000; // the scale of database
//const int nNumQuery = 10250; // the number of the queries


const int nSubBit = 8; // every 8 bits are encoded in form of byte
const int nMinNumTruth = 1; // the range of the number of the retrieved data points [nMinNumTruth, nMaxNumTruth]
const int nMaxNumTruth = 100;

char sFileName[100];
char sFileFull[100];
char sOutputDir[100];
int nChunksNum; // global variable, the number of the tables
int nMapOri[10001];  // order of the bits, usually is equal to the number of bits plus one 


struct HammingDistIdx {
	double dDist;
	UINT32 nIdx;
};

// The size of the heap is usually equal to the number of the returned data
struct Node {
	UINT32 nInd;
	double dValue;
}HeapNode[10005]; 




// sparse table
SparseHashtable *H;		// Array of m hashtables;
	
UINT32 *xornum;		// Volume of a b-bit Hamming ball with radius s (for s = 0 to d)

int power[100];		// Used within generation of binary codes at a certain Hamming distance

bitarray *counter;		// Counter for eliminating duplicate results

UINT64 *chunks;

	
struct TableNode {
	int nS;
	UINT32 nInd;
	double dValue;
};	

struct qNodeCmp {
	bool operator()(TableNode a, TableNode b) {  
		return a.dValue > b.dValue;
	}
};	
	
TableNode TableNodes[16]; // assume there are 16 tables in the extreme case
int TableOrder[16]; // assume there are 16 tables in the extreme case
priority_queue<TableNode,  vector<TableNode>, qNodeCmp> TableQue[16]; // assume there are 16 tables in the extreme case
set<UINT64> sTableCounter[16]; // assume there are 16 tables in the extreme case

	
bool compare_dist(HammingDistIdx itemA, HammingDistIdx itemB) { return (itemA.dDist < itemB.dDist); }


// calculate the delta weight	
void cal_sort_weight(const double* pWeight, const int nBits, double* dWeightDiff, byte* query, int m, int mplus) {
	double* dWeight = (double*)malloc(2 * nBits * sizeof(double));
	UINT8* pBin = (UINT8*)query;
	double dMin = 0;
	byte bBin = 0;
	int nBinCount = 0;
	
	for (int i = 0; i < nBits; i++) {
		dWeight[i * 2] = pWeight[i * 2];
		dWeight[i * 2 + 1] = pWeight[i * 2 + 1];
		
		dMin += dWeight[i * 2] < dWeight[i * 2 + 1] ? dWeight[i * 2] : dWeight[i * 2 + 1];
		
		dWeightDiff[i+1] = dWeight[i * 2] < dWeight[i * 2 + 1] ? dWeight[i * 2 + 1] - dWeight[i * 2] : dWeight[i * 2] - dWeight[i * 2 + 1];
	
		if (dWeight[i * 2] >= dWeight[i * 2 + 1]) {
			bBin += 1 << nBinCount;
		}
		
		nBinCount++;
		if (nBinCount == 8) {
			nBinCount = 0;
			pBin[(i + 1) / 8 - 1] ^= bBin;
			bBin = 0;
		}
	
	}

	int B = nBits;
	int b = ceil((double)B/m);
	int curb;
	int st = 0;
	for (int i = 0; i < m; i++) {
		if (i < mplus) curb = b;
			else curb = b - 1;
			
		for (int j = st; j < st + curb; j++)
			nMapOri[j+1] = j+1;
			
		for (int j = st; j < st + curb; j ++)
			for (int k = j + 1; k < st + curb; k++)
				if (dWeightDiff[j+1] > dWeightDiff[k+1]) {
					double t = dWeightDiff[j+1];
					dWeightDiff[j+1] = dWeightDiff[k+1];
					dWeightDiff[k+1] = t;
					int tt = nMapOri[j+1];
					nMapOri[j+1] = nMapOri[k+1];
					nMapOri[k+1] = tt;
				}
		st += curb;
	}				
	
	dWeightDiff[0] = dMin;
	free(dWeight);
}


// build the weight book 
void cal_weight(const double* pWeight, double* pWeightBook, const int nBits) {
	int n = nBits / 8;
	double dTemp[8][2];
	int nTemp[8];
	
	for (int i = 0; i < n; i++) {
		for (int j = 0; j < 8; j++) {
			for (int k = 0; k < 2; k++) {
				dTemp[j][k] = pWeight[i * 16 + j * 2 + k];
			} // k
		} // j
	
		for (int j = 0; j < 256; j++) {
			memset(nTemp, 0, sizeof(nTemp));
			int nT = 0;
			int k = j;
			while (k != 0) {
				nTemp[nT++] = k % 2;
				k = k / 2;
			}
	
			
			pWeightBook[i * 256 + j] = 0;
			for (int l = 0; l < 8; l++)
				pWeightBook[i * 256 + j] += dTemp[l][nTemp[l]];
		} // j
	} // i
}	


void heap_adjust(int i, int size) {
	int nLeft = i * 2;
	int nRight = i * 2 + 1;
	int nMax = i;
	if (i <= size / 2) {
		if (nLeft <= size && HeapNode[nMax].dValue < HeapNode[nLeft].dValue)
			nMax = nLeft;
		if (nRight <= size && HeapNode[nMax].dValue < HeapNode[nRight].dValue)
			nMax = nRight;
		if (i != nMax) {
			double t = HeapNode[nMax].dValue;
			HeapNode[nMax].dValue = HeapNode[i].dValue;
			HeapNode[i].dValue = t;
			
			int tt = HeapNode[nMax].nInd;
			HeapNode[nMax].nInd = HeapNode[i].nInd;
			HeapNode[i].nInd = tt;

			heap_adjust(nMax, size);
		}
	}
}

void build_heap(int size) {
	for (int i = size / 2; i >= 1; i--)
		heap_adjust(i, size);
}

void insert_heap(double x, UINT32 y, int size) {
	if (HeapNode[1].dValue > x) {
		HeapNode[1].dValue = x;
		HeapNode[1].nInd = y;
		heap_adjust(1, size);
	}
	
}


void asym_search_otherbits_one(const byte* pDataBin, const byte* pQueryBin, const double* pWeight,
	const int nNumData, const int nNumQuery, const int nBits, const int nNumTruth, UINT32* pNumSuccess, 
	SparseHashtable* H, bitarray* counter, const int mplus, UINT32* pCandidate, UINT32* pBucket, UINT32* pCandidate1) {
		
	UINT64 ii;
	UINT32 *arr;
	UINT8* codes;
	typedef unsigned int EntryType; //32bits, assume the number of bits can be divided by 32
	int nOffBits = 32; //32bits, assume the number of bits can be divided by 32

	EntryType* pData;
	EntryType* pQuery;

	double* pWeightBook = (double*)malloc(256 * nBits / 8 * sizeof(double));
	const int nMaxNumData = nNumTruth + 5;
	HammingDistIdx* pHammingDist = (HammingDistIdx*)malloc(nMaxNumData * sizeof(HammingDistIdx));//why 16
	double* dWeightDiff = (double*)malloc((nBits+1) * sizeof(double));
	byte* query = (byte*)malloc(sizeof(byte)*nBits/nSubBit);
	

    int m = nChunksNum;
    int size = 0;
    int s = 0;			// the growing search radius per substring
	int n = 0;
	int B = nBits;
	int b = ceil((double)B/m);
    int curb = b;		// current b: for the first mplus substrings it is b, for the rest it is (b-1)
	int nl = 0;

	

	for (int i = 0; i < m; i++) sTableCounter[i].clear();
	
	pData = (EntryType*) pDataBin;
	pQuery = (EntryType*) pQueryBin;
	
	for (int idx_query = 0; idx_query < nNumQuery; idx_query++)	{
//	for (int idx_query = 0; idx_query < 1; idx_query++)	{

		int nRadius = 0;
		int iter = 0;
		int nHeapCnt = 0;
		UINT32 nCand = 0;
		UINT32 nCand1 = 0;
		
		UINT8* pQuerySec = (UINT8*)pQuery;
		for (int j = 0; j < nBits/nSubBit; j++)
			query[j] = pQuerySec[j];

		byte* pDataSec0 = (byte*)pData;
		counter->erase();

		cal_weight(pWeight, pWeightBook, nBits);
		cal_sort_weight(pWeight, nBits, dWeightDiff, query, m, mplus);
 		
		double dDiff = 0;
		dDiff = dWeightDiff[0];
		
		split(chunks, query, m, mplus, b); // split the query into substrings
		
		//Initialization 
		//TableQue equals to the priority_queue in the table search algorithm
		//sTableCounter is used to judge if the binary code has been explored
		for (int i = 0; i < m; i++) {
			while (!TableQue[i].empty()) TableQue[i].pop();
			TableNode nn;
			nn.nS = 0; // the rightest position that the bit is changed
			nn.dValue = 0; // the increased value
			nn.nInd = 0;
			TableQue[i].push(nn);

			sTableCounter[i].clear();
			sTableCounter[i].insert(0);

		}
	
		
		n = 0;
		while (n < nNumTruth) {
			iter++;
			for (int k = 0; k < m; k++) {
				if (k < mplus)
				curb = b;
				else
				curb = b-1;
			
				TableNodes[k] = TableQue[k].top();
				TableQue[k].pop();
				TableOrder[k] = k;
				TableNode nn = TableNodes[k];
				
				// two operations
				if (nn.nS > 0 && nn.nS < curb) { // the first operation is to move the rightest position to the next one
					TableNode yy = nn;
					int ss = nn.nS + 1;
						if (k < mplus)
							yy.dValue += dWeightDiff[k*b+ss] - dWeightDiff[k*b+ss-1];
						else
							yy.dValue += dWeightDiff[mplus*b+(k-mplus)*(b-1)+ss] - dWeightDiff[mplus*b+(k-mplus)*(b-1)+ss-1];
					yy.nS = ss;
					
					int st = 0;
						if (k < mplus)
							st = k * b;
						else
							st = mplus*b+(k-mplus)*(b-1);
					
					
					yy.nInd ^= 1 << (nMapOri[st+yy.nS]-st - 1);
					yy.nInd ^= 1 << (nMapOri[st+yy.nS-1]-st - 1);
					
					if (sTableCounter[k].find(yy.nInd) == sTableCounter[k].end()) {
						sTableCounter[k].insert(yy.nInd);
						TableQue[k].push(yy);
					}
				}
					
				if (nn.nS < curb) {  // the second operation
					TableNode yy = nn;
					int ss = nn.nS + 1;
					if (k < mplus)
						yy.dValue += dWeightDiff[k*b+ss];
					else
						yy.dValue += dWeightDiff[mplus*b+(k-mplus)*(b-1)+ss];
					yy.nS = ss;
					
					
					int st = 0;
					if (k < mplus)
						st = k * b;
					else
						st = mplus*b+(k-mplus)*(b-1);
					
					yy.nInd ^= 1 << (nMapOri[st+yy.nS]-st - 1);

					if (sTableCounter[k].find(yy.nInd) == sTableCounter[k].end()) {
						sTableCounter[k].insert(yy.nInd);
						TableQue[k].push(yy);
					}
				}			
			}
		
		    /*
			// sort the table according to the delta f
			for (int i = 0; i < m; i++)
				for (int j = i+1; j < m; j++) {
					TableNode mm = TableQue[TableOrder[i]].top();
					TableNode nn = TableQue[TableOrder[j]].top();
					if (mm.dValue - TableNodes[TableOrder[i]].dValue > nn.dValue - TableNodes[TableOrder[j]].dValue) {
						int tt = TableOrder[i];
						TableOrder[i] = TableOrder[j];
						TableOrder[j] = tt;
					}
				}
			*/
				
		
			for (int i = 0; i < m; i++) {
				int k = i;
				if (k < mplus)
					curb = b;
				else
					curb = b-1;
				
				UINT64 chunksk = chunks[k];
				
				TableNode nn = TableNodes[k];
				nRadius++;

				dDiff -= nn.dValue;
				
				dDiff += TableQue[k].top().dValue;

				
				arr = H[0].query(chunksk ^ nn.nInd, &size); // lookup
				

				
				
				if (size) {			// the corresponding bucket is not empty
					for (int c = 0; c < size; c++) {
						UINT32 index = arr[c];
						nCand1++;
						
						if (!counter->get(index)) { // if it is not a duplicate
							counter->set(index);
							nCand++;
							codes = (UINT8*)pDataSec0;

							double tt = 0;
							for (int jj = 0; jj < nBits / nSubBit; jj++) {
								ii = nBits;
								ii = ii / nSubBit * index;
								tt += pWeightBook[*(pDataSec0 + ii + jj) ^ *(query + jj) + jj * 256];
						
							}
										
							if (nHeapCnt >= nNumTruth)	{
								insert_heap(tt, index, nNumTruth);
							} else {
								HeapNode[++nHeapCnt].dValue = tt;
								HeapNode[nHeapCnt].nInd = index;
								if (nHeapCnt == nNumTruth)
									build_heap(nNumTruth);
							}
							if (nHeapCnt == nNumTruth) {
								if (HeapNode[1].dValue < dDiff) {
									pCandidate[idx_query] = nCand;
									pCandidate1[idx_query] = nCand1;
									pBucket[idx_query] = nRadius;
									n = nNumTruth;
									break;
								}
							}		
						}
					}
				}
			
				if (n == nNumTruth) break;	
			
		
			}
			/*
			for (int i = 0; i < m; i++) {
				int k = i;
				TableNode nn = TableNodes[k];
				dDiff -= nn.dValue;
				nn = TableQue[k].top();
				dDiff += nn.dValue;
			}*/
			
	
			
		}		
			
		for (int i = 1; i <= nHeapCnt; i++) {
			pHammingDist[nHeapCnt - i].dDist = HeapNode[1].dValue;
			pHammingDist[nHeapCnt - i].nIdx = HeapNode[1].nInd;
			HeapNode[1].dValue = HeapNode[nHeapCnt - i + 1].dValue;
			HeapNode[1].nInd = HeapNode[nHeapCnt - i + 1].nInd;
			heap_adjust(1, nHeapCnt - i);
		}
		
	
		for (int i = 0; i < nNumTruth; i++)	{
			*pNumSuccess ++ = pHammingDist[i].nIdx;
		}
		
		pQuery += nBits / nOffBits;
		pWeight += nBits * 2;
	}

	free(pHammingDist);
	free(pWeightBook);
	free(dWeightDiff);
	free(query);
	
}	

	
void asym_search_otherbits(const byte* pDataBin, const byte* pQueryBin, const double* pWeight,
	const int nNumData, const int nNumQuery, const int nBits, const int nNumTruth, UINT32* pNumSuccess, 
	SparseHashtable* H, bitarray* counter, const int mplus, UINT32* pCandidate, UINT32* pBucket, UINT32* pCandidate1) {
		
	UINT64 ii;
	UINT32 *arr;
	UINT8* codes;
	typedef unsigned int EntryType; //32bits, assume the number of bits can be divided by 32
	int nOffBits = 32; //32bits, assume the number of bits can be divided by 32

	EntryType* pData;
	EntryType* pQuery;

	double* pWeightBook = (double*)malloc(256 * nBits / 8 * sizeof(double));
	const int nMaxNumData = nNumTruth + 5;
	HammingDistIdx* pHammingDist = (HammingDistIdx*)malloc(nMaxNumData * sizeof(HammingDistIdx));//why 16
	double* dWeightDiff = (double*)malloc((nBits+1) * sizeof(double));
	byte* query = (byte*)malloc(sizeof(byte)*nBits/nSubBit);
	

    int m = nChunksNum;
    int size = 0;
    int s = 0;			// the growing search radius per substring
	int n = 0;
	int B = nBits;
	int b = ceil((double)B/m);
    int curb = b;		// current b: for the first mplus substrings it is b, for the rest it is (b-1)
	int nl = 0;

	

	for (int i = 0; i < m; i++) sTableCounter[i].clear();
	
	pData = (EntryType*) pDataBin;
	pQuery = (EntryType*) pQueryBin;
	
	for (int idx_query = 0; idx_query < nNumQuery; idx_query++)	{
//	for (int idx_query = 0; idx_query < 1; idx_query++)	{

		int nRadius = 0;
		int iter = 0;
		int nHeapCnt = 0;
		UINT32 nCand = 0;
		UINT32 nCand1 = 0;
		
		UINT8* pQuerySec = (UINT8*)pQuery;
		for (int j = 0; j < nBits/nSubBit; j++)
			query[j] = pQuerySec[j];

		byte* pDataSec0 = (byte*)pData;
		counter->erase();

		cal_weight(pWeight, pWeightBook, nBits);
		cal_sort_weight(pWeight, nBits, dWeightDiff, query, m, mplus);
 		
		double dDiff = 0;
		dDiff = dWeightDiff[0];
		
		split(chunks, query, m, mplus, b); // split the query into substrings
		
		//Initialization 
		//TableQue equals to the priority_queue in the table search algorithm
		//sTableCounter is used to judge if the binary code has been explored
		for (int i = 0; i < m; i++) {
			while (!TableQue[i].empty()) TableQue[i].pop();
			TableNode nn;
			nn.nS = 0; // the rightest position that the bit is changed
			nn.dValue = 0; // the increased value
			nn.nInd = 0;
			TableQue[i].push(nn);

			sTableCounter[i].clear();
			sTableCounter[i].insert(0);

		}
	
		
		n = 0;
		while (n < nNumTruth) {
			iter++;
			for (int k = 0; k < m; k++) {
				if (k < mplus)
				curb = b;
				else
				curb = b-1;
			
				TableNodes[k] = TableQue[k].top();
				TableQue[k].pop();
				TableOrder[k] = k;
				TableNode nn = TableNodes[k];
				
				// two operations
				if (nn.nS > 0 && nn.nS < curb) { // the first operation is to move the rightest position to the next one
					TableNode yy = nn;
					int ss = nn.nS + 1;
						if (k < mplus)
							yy.dValue += dWeightDiff[k*b+ss] - dWeightDiff[k*b+ss-1];
						else
							yy.dValue += dWeightDiff[mplus*b+(k-mplus)*(b-1)+ss] - dWeightDiff[mplus*b+(k-mplus)*(b-1)+ss-1];
					yy.nS = ss;
					
					int st = 0;
						if (k < mplus)
							st = k * b;
						else
							st = mplus*b+(k-mplus)*(b-1);
					
					
					yy.nInd ^= 1 << (nMapOri[st+yy.nS]-st - 1);
					yy.nInd ^= 1 << (nMapOri[st+yy.nS-1]-st - 1);
					
					if (sTableCounter[k].find(yy.nInd) == sTableCounter[k].end()) {
						sTableCounter[k].insert(yy.nInd);
						TableQue[k].push(yy);
					}
				}
					
				if (nn.nS < curb) {  // the second operation
					TableNode yy = nn;
					int ss = nn.nS + 1;
					if (k < mplus)
						yy.dValue += dWeightDiff[k*b+ss];
					else
						yy.dValue += dWeightDiff[mplus*b+(k-mplus)*(b-1)+ss];
					yy.nS = ss;
					
					
					int st = 0;
					if (k < mplus)
						st = k * b;
					else
						st = mplus*b+(k-mplus)*(b-1);
					
					yy.nInd ^= 1 << (nMapOri[st+yy.nS]-st - 1);

					if (sTableCounter[k].find(yy.nInd) == sTableCounter[k].end()) {
						sTableCounter[k].insert(yy.nInd);
						TableQue[k].push(yy);
					}
				}			
			}
		
		    /*
			// sort the table according to the delta f
			for (int i = 0; i < m; i++)
				for (int j = i+1; j < m; j++) {
					TableNode mm = TableQue[TableOrder[i]].top();
					TableNode nn = TableQue[TableOrder[j]].top();
					if (mm.dValue - TableNodes[TableOrder[i]].dValue > nn.dValue - TableNodes[TableOrder[j]].dValue) {
						int tt = TableOrder[i];
						TableOrder[i] = TableOrder[j];
						TableOrder[j] = tt;
					}
				}
			*/
				
		
			for (int i = 0; i < m; i++) {
				int k = i;
				if (k < mplus)
					curb = b;
				else
					curb = b-1;
				
				UINT64 chunksk = chunks[k];
				
				TableNode nn = TableNodes[k];
				nRadius++;

				dDiff -= nn.dValue;
				
				dDiff += TableQue[k].top().dValue;

				
				arr = H[0].query(chunksk ^ nn.nInd, &size); // lookup
				

				
				
				if (size) {			// the corresponding bucket is not empty
					for (int c = 0; c < size; c++) {
						UINT32 index = arr[c];
						nCand1++;
						
						if (!counter->get(index)) { // if it is not a duplicate
							counter->set(index);
							nCand++;
							codes = (UINT8*)pDataSec0;

							double tt = 0;
							for (int jj = 0; jj < nBits / nSubBit; jj++) {
								ii = nBits;
								ii = ii / nSubBit * index;
								tt += pWeightBook[*(pDataSec0 + ii + jj) ^ *(query + jj) + jj * 256];
						
							}
										
							if (nHeapCnt >= nNumTruth)	{
								insert_heap(tt, index, nNumTruth);
							} else {
								HeapNode[++nHeapCnt].dValue = tt;
								HeapNode[nHeapCnt].nInd = index;
								if (nHeapCnt == nNumTruth)
									build_heap(nNumTruth);
							}

						}
					}
				}
			
				//if (n == nNumTruth) break;	
				if (nHeapCnt == nNumTruth) {
					if (HeapNode[1].dValue <= dDiff) {
						pCandidate[idx_query] = nCand;
						pCandidate1[idx_query] = nCand1;
						pBucket[idx_query] = nRadius;
						n = nNumTruth;
						break;
					}			
				}		
		
			}
			/*
			for (int i = 0; i < m; i++) {
				int k = i;
				TableNode nn = TableNodes[k];
				dDiff -= nn.dValue;
				nn = TableQue[k].top();
				dDiff += nn.dValue;
			}*/
			
	
			
		}		
			
		for (int i = 1; i <= nHeapCnt; i++) {
			pHammingDist[nHeapCnt - i].dDist = HeapNode[1].dValue;
			pHammingDist[nHeapCnt - i].nIdx = HeapNode[1].nInd;
			HeapNode[1].dValue = HeapNode[nHeapCnt - i + 1].dValue;
			HeapNode[1].nInd = HeapNode[nHeapCnt - i + 1].nInd;
			heap_adjust(1, nHeapCnt - i);
		}
		
	
		for (int i = 0; i < nNumTruth; i++)	{
			*pNumSuccess ++ = pHammingDist[i].nIdx;
		}
		
		pQuery += nBits / nOffBits;
		pWeight += nBits * 2;
	}

	free(pHammingDist);
	free(pWeightBook);
	free(dWeightDiff);
	free(query);
	
}	
	

void write_file(char sFileName[], UINT32* pNumSuccess, int nNumTruth) {
	printf("file name:%s\n", sFileName);
	FILE* fp;
	fp=fopen(sFileName, "wb"); 
    if(fp==NULL) {
	  printf("fail!\n");
	  exit(1); 
    }	
	
	for (int i = 0; i < nNumQuery * nNumTruth; i++)
			fwrite(&pNumSuccess[i], sizeof(UINT32), 1, fp);
	
	
	fclose(fp);
	
}

void write_candidate_file(char sFileName[], UINT32* pCandidate) {
	printf("file name:%s\n", sFileName);
	FILE* fp;
	fp=fopen(sFileName, "w");
    if(fp==NULL) {
	  printf("fail!\n");
	  exit(1); 
    }	
	
	for (int i = 0; i < nNumQuery; i++)
		fprintf(fp, "%u\n", pCandidate[i]);
	fclose(fp);
	
}

void write_radius_file(char sFileName[], UINT32* pBucket) {
	printf("file name:%s\n", sFileName);
	FILE* fp;
	fp=fopen(sFileName, "w"); 
    if(fp==NULL) {
	  printf("fail!\n");
	  exit(1); 
    }	
	
	for (int i = 0; i < nNumQuery; i++)
		fprintf(fp, "%u\n", pBucket[i]);
	fclose(fp);
	
}



void read_weight_file(char sFileName[], double* pWeight, int nBits)
{
	// for binary file
	 

	printf("file name:%s\n", sFileName);
	FILE* fp;
	fp=fopen(sFileName, "rb"); 
    if(fp==NULL) {
	  printf("fail to read the file!\n");
	  exit(1); //
    }	
	
	int n;
	double f;
	for (int k = 0; k < nNumQuery; k++)
		for (int i = 0; i < nBits; i++)
			for (int j = 0; j < 2; j++) {
				if(fread(&f, sizeof(double), 1, fp)!=1) {
					printf("fail to write the file\n");  
					exit(0);
				}
				pWeight[k * nBits * 2 + i * 2 + j] = f;
			}	
	fclose(fp);	
	
	
	// for text file
	/*
	printf("file name:%s\n", sFileName);
	FILE* fp;
	fp=fopen(sFileName, "r"); 
    if(fp==NULL) {
	  printf("fail to read the file!\n");
	  exit(1); //
    }	
	
	int n;
	double f;
	for (int k = 0; k < nNumQuery; k++)
		for (int i = 0; i < nBits; i++)
			for (int j = 0; j < 2; j++) {
				fscanf(fp, "%lf", &f);
				pWeight[k * nBits * 2 + i * 2 + j] = f;
			}
	fclose(fp);		
	*/	
}

void read_data_file(char sFileName[], byte* pDataBin, int nBytes)
{

	// for binary file
    
	printf("file name:%s\n", sFileName);
	FILE* fp;
	fp=fopen(sFileName, "rb"); 
    if(fp==NULL) 
    {
	  printf("fail to read the file!\n");
	  exit(1); 
    }	
	
	int n;
	for (int i = 0; i < nNumData; i++)
	{

		for (int j = 0; j < nBytes; j++)
		{
			UINT64 ii = i;
			if(fread(&pDataBin[ii*nBytes+j], sizeof(byte), 1, fp)!=1)  
			{
				printf("fail to write the file\n");
				exit(0);
			}				
		}
	}
	fclose(fp);	
	
	
	// for text file
	/*
	printf("file name:%s\n", sFileName);
	FILE* fp;
	fp=fopen(sFileName, "r"); 
    if(fp==NULL) {
	  printf("fail to read the file!\n");
	  exit(1); 
    }	
	
	int n;
	for (int i = 0; i < nNumData; i++) {

		for (int j = 0; j < nBytes; j++) {
			UINT64 ii = i;
			int d;
			fscanf(fp, "%d", &d);
			pDataBin[ii*nBytes+j] = (byte) d;
		}
	}
	fclose(fp);		
	*/
}

void read_query_file(char sFileName[], byte* pQueryBin, int nBytes)
{

	// for binary file
    

	printf("file name:%s\n", sFileName);
	FILE* fp;
	fp=fopen(sFileName, "rb"); 
    if(fp==NULL) 
    {
	  printf("fail to read the file!\n");
	  exit(1); 
    }	
	
	int n;
	for (int i = 0; i < nNumQuery; i++)
	{

		for (int j = 0; j < nBytes; j++)
		{
			if(fread(&pQueryBin[i*nBytes+j], sizeof(byte), 1, fp)!=1)  
			{
				printf("fail to write the file\n");  
				exit(0);
			}

		}
	}
	fclose(fp);	
	
	// for text file
	/*
	printf("file name:%s\n", sFileName);
	FILE* fp;
	fp=fopen(sFileName, "r"); 
    if(fp==NULL) {
	  printf("fail to read the file!\n");
	  exit(1); 
    }	
	
	int n;
	for (int i = 0; i < nNumQuery; i++) {

		for (int j = 0; j < nBytes; j++) {
			int d;
			fscanf(fp, "%d", &d);
			pQueryBin[i*nBytes+j] = (byte) d;
		}
	}
	fclose(fp);		
	*/
}



void write_time_file(char sFileName[], double dTime)
{
	printf("file name:%s\n", sFileName);
	FILE* fp;
	fp=fopen(sFileName, "w"); 
    if(fp==NULL) {
	  printf("fail to write the file\n");
	  exit(1); 
    }	
	fprintf(fp, "%.5lf\n", dTime);	
	fclose(fp);
	
}

	

int main(int argc, char* argv[])
{
	int nByte = 32;
	if (argc != 0) {
		nByte = atoi(argv[1]);
		printf("bit number: %d\n", nByte);
	}
	
	
	UINT64 ii;
	for (int nBytes = 2; nBytes <= 2; nBytes *= 2) {
		nBytes = nByte / 8;
		int nBits = nBytes * 8;
		int nSt = nBits / 16; // the range of the length of substrings, CIFAR-10: nbits / 8, GIST1M: nbits / 16
		int nEd = nBits / 16;
		for (int f = nSt; f >= nEd; f--) {
			nChunksNum = f;
			double* pWeight = (double*)malloc(nBits * 2 * nNumQuery * sizeof(double));
			ii = nNumData;
			ii = ii * nBytes * sizeof(byte);
			byte* pDataBin = (byte*)malloc(ii);
			byte* pQueryBin = (byte*)malloc(nNumQuery * nBytes * sizeof(byte));
		
			

			sprintf(sFileName, "bit_weight%d\0", nBits);
			strcpy(sFileFull, sFileDir);
			strcat(sFileFull, sFileName);
			read_weight_file(sFileFull, pWeight, nBits);
	
			sprintf(sFileName, "databin%d\0", nBits);
			strcpy(sFileFull, sFileDir);
			strcat(sFileFull, sFileName);
			read_data_file(sFileFull, pDataBin, nBytes);
	
			sprintf(sFileName, "querybin%d\0", nBits);
			strcpy(sFileFull, sFileDir);
			strcat(sFileFull, sFileName);
			read_query_file(sFileFull, pQueryBin, nBytes);
		
			printf("nNumData: %d\n", nNumData);
			printf("nNumQueries: %d\n", nNumQuery);
			printf("nBytes: %d\n", nBytes);
		
			// introducing the sparse_hashtable
			counter = new bitarray;
			counter->init(nNumData);

			double dSortTime = 0;
			double dMapTime = 0;
			double dRecallTime = 0;
			int B = nBits;
			int m = nChunksNum;
			int b = ceil((double)nBits/m);
 
			int D = ceil(nBits/2.0);		// assuming that B/2 is large enough radius to include all of the k nearest neighbors
			int d = ceil((double)D*2/m);
   
			int mplus = B - m * (b-1);
			printf("mpllus %d\n", mplus);
			xornum = new UINT32 [d+2];
			xornum[0] = 0;
			for (int i=0; i<=d; i++)
				xornum[i+1] = xornum[i] + choose(b, i);
		
			H = new SparseHashtable[1];
			for (int i=0; i<1; i++)
				H[i].init(b);
			//for (int i=mplus; i<m; i++)
			//	H[i].init(b-1);		
	
			chunks = new UINT64[m];
			int N = nNumData;
			int dim1codes = nBits / 8;
		
			UINT8 * pcodes = (UINT8*) pDataBin;

			for (UINT64 i=0; i<N; i++) {
				split(chunks, pcodes, m, mplus, b);
				//H[k].count_insert(chunks[k], i);
				for (int j = 0; j < m; j++) {
					bool u = true;
					for (int l = 0; l < j; l++)
						if (chunks[j] == chunks[l]) u = false;
					if (u)
						H[0].count_insert(chunks[j], i);
				}
					
				if (i % (int)ceil((double)N/1000) == 0) {
					printf("%.2f%%\r", (double)i/N * 100);
					fflush(stdout);
				}
				pcodes += dim1codes;
			}

			pcodes = (UINT8*) pDataBin;
			for (UINT64 i=0; i<N; i++) {
				split(chunks, pcodes, m, mplus, b);

				//H[k].data_insert(chunks[k], i);
				for (int j = 0; j < m; j++) {
					bool u = true;
					for (int l = 0; l < j; l++)
						if (chunks[j] == chunks[l]) u = false;
					if (u) H[0].data_insert(chunks[j], i);
				}

				if (i % (int)ceil((double)N/1000) == 0) {
					printf("%.2f%%\r", (double)i/N * 100);
					fflush(stdout);
				}
				pcodes += dim1codes;
			}
	
		
			printf("size of table: %d\n", sizeof(H[0]));
			for (int nNumTruth = nMinNumTruth; nNumTruth <= nMaxNumTruth; nNumTruth *= 10) { // return different numbers of data points
				UINT32* pNumSuccess = (UINT32*)malloc(nNumQuery * nNumTruth * sizeof(UINT32));
				UINT32* pCandidate = (UINT32*)malloc(nNumQuery * sizeof(UINT32));
				UINT32* pCandidate1 = (UINT32*)malloc(nNumQuery * sizeof(UINT32));
				UINT32* pBucket = (UINT32*)malloc(nNumQuery * sizeof(UINT32));
				clock_t tSt, tEd;
				
				// sort the data
				tSt = clock();
				if (nBits % 8 == 0)	{
					printf("begin query\n");
					if (m == 1)
						asym_search_otherbits_one(pDataBin, pQueryBin, pWeight, nNumData, nNumQuery, nBits, nNumTruth, pNumSuccess, H, counter, mplus, pCandidate, pBucket, pCandidate1);
					else
						asym_search_otherbits(pDataBin, pQueryBin, pWeight, nNumData, nNumQuery, nBits, nNumTruth, pNumSuccess, H, counter, mplus, pCandidate, pBucket, pCandidate1);
				} else printf("Wrong bit number\n");
				tEd = clock();
				dSortTime = (double)(tEd - tSt) / CLOCKS_PER_SEC;
				
				printf("query time: %.5lf\n", dSortTime / nNumQuery);
				
				sprintf(sOutputDir, "%s%d/\0", sFileDir, nBits);
				sprintf(sFileName, "MIWQ_one%d_%d_%d_%d_%d\0", nBits, nNumTruth, nChunksNum, nNumData, nNumQuery); 
				strcpy(sFileFull, sOutputDir);
				strcat(sFileFull, sFileName);
				write_file(sFileFull, pNumSuccess, nNumTruth);

				sprintf(sFileName, "time_MIWQ_one%d_%d_%d_%d_%d.txt\0", nBits, nNumTruth, nChunksNum, nNumData, nNumQuery); 
				strcpy(sFileFull, sOutputDir);
				strcat(sFileFull, sFileName);
				write_time_file(sFileFull, dSortTime / nNumQuery);
				
				sprintf(sFileName, "candidate_MIWQ_one%d_%d_%d_%d_%d.txt\0", nBits, nNumTruth, nChunksNum, nNumData, nNumQuery); 
				strcpy(sFileFull, sOutputDir);
				strcat(sFileFull, sFileName);
				write_candidate_file(sFileFull, pCandidate);
				
				sprintf(sFileName, "bucket_MIWQ_one%d_%d_%d_%d_%d.txt\0", nBits, nNumTruth, nChunksNum, nNumData, nNumQuery); 
				strcpy(sFileFull, sOutputDir);
				strcat(sFileFull, sFileName);
				write_radius_file(sFileFull, pBucket);

				sprintf(sFileName, "ori_candidate_MIWQ_one%d_%d_%d_%d_%d.txt\0", nBits, nNumTruth, nChunksNum, nNumData, nNumQuery); 
				strcpy(sFileFull, sOutputDir);
				strcat(sFileFull, sFileName);
				write_candidate_file(sFileFull, pCandidate1);

                double ave = 0;
				for (int iQuery = 0; iQuery < nNumQuery; iQuery++) {
					ave += pCandidate[iQuery];
				}
				ave /= nNumQuery;
				sprintf(sFileName, "ave_candidate_MIWQ_one%d_%d_%d_%d_%d.txt\0", nBits, nNumTruth, nChunksNum, nNumData, nNumQuery); 
				strcpy(sFileFull, sOutputDir);
				strcat(sFileFull, sFileName);
				write_time_file(sFileFull, ave);

				ave = 0;
				for (int iQuery = 0; iQuery < nNumQuery; iQuery++) {
					ave += pCandidate1[iQuery];
				}
				ave /= nNumQuery;
				sprintf(sFileName, "ave_ori_candidate_MIWQ_one%d_%d_%d_%d_%d.txt\0", nBits, nNumTruth, nChunksNum, nNumData, nNumQuery); 
				strcpy(sFileFull, sOutputDir);
				strcat(sFileFull, sFileName);
				write_time_file(sFileFull, ave);

				ave = 0;
				for (int iQuery = 0; iQuery < nNumQuery; iQuery++) {
					ave += pBucket[iQuery];
				}
				ave /= nNumQuery;
				sprintf(sFileName, "ave_bucket_MIWQ_one%d_%d_%d_%d_%d.txt\0", nBits, nNumTruth, nChunksNum, nNumData, nNumQuery); 
				strcpy(sFileFull, sOutputDir);
				strcat(sFileFull, sFileName);
				write_time_file(sFileFull, ave);

				
				free(pNumSuccess);
				free(pCandidate);
				free(pCandidate1);
				free(pBucket);
			}
			delete [] H;
			delete [] xornum;
			delete counter;
			delete [] chunks;
		
			free(pDataBin);
			free(pQueryBin);
			free(pWeight);
		}
	}
	return 0;
}
