///  \file
///  \brief  Algorithms that impose (global) constraints over arrays of
///           constrained variables.
///
///  \internal
///  This file is part of
///   <span style="font-variant: small-caps;"> Naxos Solver: </span>
///   A Constraint Programming Library. \n
///   Copyright ? 2007-2010  Nikolaos Pothitos.
///
///  See ../license/LICENSE for the license of the library.





#include "naxos.h"
#include "internal.h"
#include <cstdlib>


using namespace naxos;
using namespace std;



	void
array_min_minmax (const NsIntVarArray *VarArr, NsInt& min, NsInt& minmax)
{
	NsIntVarArray::const_iterator  V = VarArr->begin();
	min = V->min();
	minmax = V->max();
	++V;
	for ( ;   V != VarArr->end();   ++V)   {
		if (V->min() < min)
			min = V->min();
		if (V->max() < minmax)
			minmax = V->max();
	}
}

	void
array_maxmin_max (const NsIntVarArray *VarArr, NsInt& maxmin, NsInt& max)
{
	NsIntVarArray::const_iterator  V = VarArr->begin();
	maxmin = V->min();
	max = V->max();
	++V;
	for ( ;   V != VarArr->end();   ++V)   {
		if (V->min() > maxmin)
			maxmin = V->min();
		if (V->max() > max)
			max = V->max();
	}
}

	void
array_sum_min_max (const NsIntVarArray *VarArr, const NsIndex start, const NsIndex length,
			NsInt& sumMin, NsInt& sumMax)
{
	sumMin = sumMax = 0;
	for (NsIndex  i=start;   i < start+length;   ++i)   {
		const NsIntVar&  V = (*VarArr)[i];
		sumMin += V.min();
		sumMax += V.max();
	}
	//for (NsIntVarArray::iterator V = VarArr->begin();   V != VarArr->end();   ++V)   {
	//	sumMin += V->min();
	//	sumMax += V->max();
	//}
}



Ns_ConstrXeqMin::Ns_ConstrXeqMin (NsIntVar *X, NsIntVarArray *VarArr_init)
		: VarX(X), VarArr(VarArr_init)
{
	revisionType  =  BIDIRECTIONAL_CONSISTENCY;


	assert_Ns( ! VarArr->empty() ,
			"Ns_ConstrXeqMin::Ns_ConstrXeqMin: Empty `VarArr'");

	NsProblemManager&  pm = VarX->manager();

	for (NsIntVarArray::iterator  V = VarArr->begin();   V != VarArr->end();   ++V)   {
		assert_Ns( &pm == &V->manager(),  "Ns_ConstrXeqMin::Ns_ConstrXeqMin: All the variables of a constraint must belong to the same NsProblemManager");
	}
}





Ns_ConstrXeqMax::Ns_ConstrXeqMax (NsIntVar *X, NsIntVarArray *VarArr_init)
		: VarX(X), VarArr(VarArr_init)
{
	revisionType  =  BIDIRECTIONAL_CONSISTENCY;


	assert_Ns( ! VarArr->empty() ,
			"Ns_ConstrXeqMax::Ns_ConstrXeqMax: Empty `VarArr'");

	NsProblemManager&  pm = VarX->manager();

	for (NsIntVarArray::iterator  V = VarArr->begin();   V != VarArr->end();   ++V)   {
		assert_Ns( &pm == &V->manager(),  "Ns_ConstrXeqMax::Ns_ConstrXeqMax: All the variables of a constraint must belong to the same NsProblemManager");
	}
}


	void
Ns_ConstrXeqMin::ArcCons (void)
{
	NsInt  min, minmax;
	array_min_minmax(VarArr, min, minmax);

	VarX->removeRange(minmax+1, NsPLUS_INF, this);

	do  {
		if ( ! VarX->removeRange(NsMINUS_INF, min-1, this) )
			return;

		NsIntVarArray::iterator  V = VarArr->begin();
		min  =  V->min();

		for ( ;   V != VarArr->end();  ++V)   {

			if ( ! V->removeRange(NsMINUS_INF, VarX->min()-1, this) )
				return;

			if ( V->min()  <  min )
				min  =  V->min();
		}
	} while ( min  >  VarX->min() );


	//NsIntVarArray::iterator  V;
	//NsIntVar::const_iterator v = VarX->begin();
	//++v;	// the first value is OK
	//for ( ;  v != VarX->end();  ++v)   {

	//	for (V = VarArr->begin();   V != VarArr->end();   ++V)   {
	//		if ( V->contains( *v ) )
	//			break;
	//	}

	//	if ( V  ==  VarArr->end() )
	//		VarX->removeSingle( *v , this);
	//}
}


	void
Ns_ConstrXeqMax::ArcCons (void)
{
	NsInt  maxmin, max;
	array_maxmin_max(VarArr, maxmin, max);

	VarX->removeRange(NsMINUS_INF, maxmin-1, this);

	do  {
		if ( ! VarX->removeRange(max+1, NsPLUS_INF, this) )
			return;

		NsIntVarArray::iterator  V = VarArr->begin();
		max  =  V->max();

		for ( ;   V != VarArr->end();   ++V)    {

			if ( ! V->removeRange(VarX->max()+1, NsPLUS_INF, this) )
				return;

			if ( V->max()  >  max )
				max  =  V->max();
		}
	} while ( max  <  VarX->max() );


	//NsIntVarArray::iterator  V;
	//NsIntVar::const_iterator v = VarX->begin();
	//++v;	// the first value is OK
	//for ( ;  v != VarX->end();  ++v)   {

	//	for (V = VarArr->begin();   V != VarArr->end();   ++V)   {
	//		if ( V->contains( *v ) )
	//			break;
	//	}

	//	if ( V  ==  VarArr->end() )
	//		VarX->removeSingle( *v , this);
	//}
}








	void
Ns_ConstrXeqMin::LocalArcCons (Ns_QueueItem& Qitem)
{
	ArcCons();


	//NsIntVarArray::iterator  V;

	//if ( VarX  ==  Qitem.getVarFired() )    {

	//	//if ( Qitem.getW()  <  VarX->min() )  {

	//		for (V = VarArr->begin();   V != VarArr->end();   ++V)
	//			V->removeRange(NsMINUS_INF, VarX->min()-1, this);
	//	//}


	//}  else  {

	//	//if ( Qitem.getW()  >  Qitem.getVarFired()->max() )

	//	VarX->removeRange(Qitem.getVarFired()->max()+1, NsPLUS_INF, this);

	//	if ( Qitem.getVarFired()->min()  >  VarX->min() )    {

	//		NsInt  min, minmax;
	//		array_min_minmax(VarArr, min, minmax);

	//		VarX->removeRange(NsMINUS_INF, min-1, this);
	//		VarX->removeRange(minmax+1, NsPLUS_INF, this);

	//		//for (V = VarArr->begin();
	//		//		V != VarArr->end();
	//		//		++V)
	//		//{
	//		//	if ( V->min()  <=  VarX->min() )
	//		//		break;
	//		//}

	//		//if ( V  ==  VarArr->end() )    {

	//		//	VarX->remove(NsMINUS_INF,
	//		//		Qitem.getVarFired()->min()-1, this);
	//		//}
	//	}

	//	//if ( VarX->contains(Qitem.getW()) )   {

	//	//	for (V = VarArr->begin();   V != VarArr->end();   ++V)   {

	//	//		if ( V->contains( Qitem.getW() ) )
	//	//			break;
	//	//	}

	//	//	if ( V  ==  VarArr->end() )
	//	//		VarX->removeSingle( Qitem.getW() , this);
	//	//}
	//}
}




	void
Ns_ConstrXeqMax::LocalArcCons (Ns_QueueItem& Qitem)
{
	ArcCons();


	//NsIntVarArray::iterator  V;

	//if ( VarX  ==  Qitem.getVarFired() )    {

	//	//if ( Qitem.getW() > VarX->max() )    {
	//		for (V = VarArr->begin();   V != VarArr->end();   ++V)
	//			V->removeRange(VarX->max()+1, NsPLUS_INF, this);
	//	//}

	//}  else  {

	//	//if ( Qitem.getW() < Qitem.getVarFired()->min() )    {
	//	VarX->removeRange(NsMINUS_INF, Qitem.getVarFired()->min()-1, this);
	//	//}

	//	if ( Qitem.getVarFired()->max()  <  VarX->max() )    {

	//		NsInt  maxmin, max;
	//		array_maxmin_max(VarArr, maxmin, max);

	//		VarX->removeRange(NsMINUS_INF, maxmin-1, this);
	//		VarX->removeRange(max+1, NsPLUS_INF, this);

	//		//for (V = VarArr->begin();
	//		//		V != VarArr->end();
	//		//		++V)
	//		//{
	//		//	if ( V->max()  >=  VarX->max() )
	//		//		break;
	//		//}

	//		//if ( V  ==  VarArr->end() )    {

	//		//	VarX->removeRange(Qitem.getVarFired()->max()+1,
	//		//			NsPLUS_INF, this);
	//		//}
	//	}


	//	//if ( VarX->contains(Qitem.getW()) )    {

	//	//	for (V = VarArr->begin();   V != VarArr->end();   ++V)   {
	//	//		if ( V->contains( Qitem.getW() ) )
	//	//			break;
	//	//	}

	//	//	if ( V  ==  VarArr->end() )
	//	//		VarX->removeSingle( Qitem.getW() , this);
	//	//}
	//}
	//		//for (V = VarArr->begin();
	//		//		V != VarArr->end();
	//		//		++V)
	//		//{
	//		//	if ( ! V->isBound() )
	//		//		break;
	//		//}

	//		//if ( V  ==  VarArr->end()  &&  ! VarX->isBound() )
	//		//	cout << VarX << "  =  max" << VarArr << "\n";
}






Ns_ConstrXeqSum::Ns_ConstrXeqSum (NsIntVar *X, NsIntVarArray *VarArr_init)
		: /*Ns_Constraint(2),*/ VarX(X), VarArr(VarArr_init),
		  start(0), length(VarArr_init->size())
{
	assert_Ns( ! VarArr->empty() ,
			"Ns_ConstrXeqSum::Ns_ConstrXeqSum: Empty `VarArr'");

	NsProblemManager&  pm = VarX->manager();

	for (NsIntVarArray::iterator  V = VarArr->begin();   V != VarArr->end();   ++V)   {
		assert_Ns( &pm == &V->manager(),  "Ns_ConstrXeqSum::Ns_ConstrXeqSum: All the variables of a constraint must belong to the same NsProblemManager");
	}
}



Ns_ConstrXeqSum::Ns_ConstrXeqSum (NsIntVar *X, NsIntVarArray *VarArr_init,
		const NsIndex start_init, const NsIndex length_init)
		: /*Ns_Constraint(2),*/ VarX(X), VarArr(VarArr_init), start(start_init), length(length_init)
{
	revisionType  =  BIDIRECTIONAL_CONSISTENCY;


	assert_Ns( ! VarArr->empty() ,
			"Ns_ConstrXeqSum::Ns_ConstrXeqSum: Empty `VarArr'");

	NsProblemManager&  pm = VarX->manager();

	for (NsIndex  i=start;   i < start+length;   ++i)   {
		NsIntVar&  V = (*VarArr)[i];
		assert_Ns( &pm == &V.manager(),  "Ns_ConstrXeqSum::Ns_ConstrXeqSum: All the variables of a constraint must belong to the same NsProblemManager");
	}
}


// bounds-consistency only
	void
Ns_ConstrXeqSum::ArcCons (void)
{
	NsInt  sumMin, sumMax;
	array_sum_min_max(VarArr, start, length, sumMin, sumMax);
	NsIndex  i;

	bool  changed_summinmax = true;

	for ( ; ; )  {
		do  {
			if ( ! VarX->removeRange(NsMINUS_INF, sumMin-1, this) )
				return;

			for (i = start;   i < start+length;   ++i)   {
				NsIntVar&  V = (*VarArr)[i];
				if ( V.min() + sumMax - V.max() < VarX->min() )   {
					sumMin -= V.min();
					if ( ! V.removeRange(NsMINUS_INF,  - sumMax + V.max() + VarX->min() -1, this) )
						return;
					sumMin += V.min();
					changed_summinmax = true;
				}
			}

		} while (VarX->min() < sumMin);

		//  Initially `changed_summinmax' was intentionally set true, in order the
		//   following `if' statement to be ignored, the first time it is executed.
		if ( ! changed_summinmax )
			break;
		changed_summinmax = false;

		do  {
			if ( ! VarX->removeRange(sumMax+1, NsPLUS_INF, this) )
				return;

			for (i = start;   i < start+length;   ++i)   {
				NsIntVar&  V = (*VarArr)[i];
				if ( V.max() + sumMin - V.min() > VarX->max() )   {
					sumMax -= V.max();
					if ( ! V.removeRange(- sumMin + V.min() + VarX->max() +1,  NsPLUS_INF, this) )
						return;
					sumMax += V.max();
					changed_summinmax = true;
				}
			}

		} while (VarX->max() > sumMax);

		if ( ! changed_summinmax )
			break;
		changed_summinmax = false;
	}
}


// bounds-consistency only
	void
Ns_ConstrXeqSum::LocalArcCons (Ns_QueueItem& Qitem)
{
	//if (Qitem.getVarFired()->min() < Qitem.getW()  &&  Qitem.getW() < Qitem.getVarFired()->max())
	//	return;	// bounds-consistency does not care

	ArcCons();
	//throw  NsException("Ns_ConstrXeqSum::LocalArcCons: unimplemented");
}











//#ifndef Ns_AllDiff_Test


Ns_ConstrAllDiff::Ns_ConstrAllDiff (NsIntVarArray *VarArr_init)
	: VarArr(VarArr_init)
{
	assert_Ns( VarArr->size() >= 2 ,
			"Ns_ConstrAllDiff::Ns_ConstrAllDiff: Condition required:  VarArr.size() >= 2");

	NsIntVarArray::iterator  X = VarArr->begin();
	NsProblemManager&  pm = X->manager();
	++X;

	for ( ;   X != VarArr->end();   ++X)  {
		assert_Ns( &pm == &X->manager(),  "Ns_ConstrAllDiff::Ns_ConstrAllDiff: All the variables of a constraint must belong to the same NsProblemManager");
	}
}




namespace  {

		void
	allDiffArcCons (NsIntVarArray *VarArr,
			NsQueue<const NsIntVar*>& newBoundVars,
			const Ns_Constraint *constraint)
	{
		while ( ! newBoundVars.empty() )    {

			NsInt  val = newBoundVars.front()->value();

			for (NsIntVarArray::iterator X = VarArr->begin();
					X != VarArr->end();
					++X)
			{
				bool  wasBound = X->isBound();

				if ( &*X  !=  newBoundVars.front() )
					X->removeSingle( val, constraint );

				if ( ! wasBound  &&  X->isBound() )
					newBoundVars.push( &*X );
			}

			newBoundVars.pop();
		}
	}

} // namespace



	void
Ns_ConstrAllDiff::ArcCons (void)
{
	NsIntVarArray::iterator  X, Y;

	// Dovecote Theorem (to spot a dead-end earlier) //
	NsInt  min_of_arr, max_of_arr;

	X = VarArr->begin();
	min_of_arr = X->min();
	max_of_arr = X->max();
	++X;

	for ( ;   X != VarArr->end();   ++X)  {
		if (X->min() < min_of_arr)
			min_of_arr = X->min();
		if (X->max() > max_of_arr)
			max_of_arr = X->max();
	}

	if ( static_cast<NsUInt>(max_of_arr - min_of_arr) + 1  <  VarArr->size() )    {

		VarArr->begin()->removeAll();	// all values are inconsistent
		return;
	}


	// Classic ArcCons //

	NsQueue<const NsIntVar*>  newBoundVars;

	for (X = VarArr->begin();   X != VarArr->end();   ++X)    {

		if ( X->isBound() )
			newBoundVars.push( &*X );
	}

	allDiffArcCons(VarArr, newBoundVars, this);

	//for (X = VarArr->begin();   X != VarArr->end();   ++X)  {
	//	for (Y = VarArr->begin();   Y != VarArr->end();   ++Y)  {
	//		if ( Y != X   &&   Y->isBound() )
	//			X->removeSingle( Y->value(), 0 );
	//		//  `0' is used in order not to record this constraint
	//		//   that provoked the removal, because
	//		//   Ns_ConstrAllDiff::LocalArcCons() should be called
	//		//   to check again the constraint AllDiff (against
	//		//   this removal).
	//	}
	//}
}


	void
Ns_ConstrAllDiff::LocalArcCons (Ns_QueueItem& Qitem)
{
	if ( Qitem.getVarFired()->isBound() )    {

		NsQueue<const NsIntVar*>  newBoundVars;

		newBoundVars.push( Qitem.getVarFired() );

		allDiffArcCons(VarArr, newBoundVars, this);
	}


	//if ( Qitem.getVarFired()->isBound() )    {

	//	NsInt  Value = Qitem.getVarFired()->value();

	//	for (NsIntVarArray::iterator X = VarArr->begin();   X != VarArr->end();   ++X)  {
	//		if ( &*X  !=  Qitem.getVarFired() )
	//			X->removeSingle( Value, 0 );
	//		//  `0' is used in order not to record this constraint...
	//		//   (see the previous comment).
	//	}
	//}
}


//#endif  // ! Ns_AllDiff_Test






	bool
Ns_ConstrAllDiffStrong::groupedNsIntVar::removeDomain (const NsIntVar& V, const Ns_Constraint *constraint)
{
	if ( Var.max()  <=  V.max() )   {

		//  In this case, and when we have bounds-consistency mode (i.e. a
		//   constrained variable is represented by its minimum and maximum),
		//   we `eat' the values from `right' to `left', in order not to avoid
		//   (if possible) removing a value from the middle of the domain.

		for (NsIntVar::const_reverse_iterator val = V.rbegin();  val != V.rend();   ++val)    {

			//if ( Var.contains(*val) )   {

				if ( ! Var.removeSingle( *val , constraint ) )
					return  false;
			//}
		}


	} else   {

	      for (NsIntVar::const_iterator val = V.begin();  val != V.end();   ++val)    {

	      	//if ( Var.contains(*val) )   {

	      		if ( ! Var.removeSingle(*val, constraint) )
	      			return  false;
	      	//}
	      }
	}

	return  true;
}











//struct less_max_mmin_size : public binary_function<NsIntVar, NsIntVar, bool>  {
//
//	bool  operator ()  (const MaxLopez& X, const MaxLopez& Y)
//	{
//		return  ( X.max() < Y.max()
//				|| ( X.max() == Y.max()  &&  X.min() >  Y.min() )
//				|| ( X.max() == Y.max()  &&  X.min() == Y.min()  &&  X.size() < Y.size() ) );
//	}
//
//};
//
//
//struct less_min           : public binary_function<NsIntVar, NsIntVar, bool>  {
//
//	bool  operator ()  (const MaxLopez& X, const MaxLopez& Y)
//	{
//		return  ( X.min() >  Y.min() );
//	}
//
//};



//#ifdef Ns_AllDiff_Test


Ns_ConstrAllDiffStrong::Ns_ConstrAllDiffStrong (NsIntVarArray *VarArr_init, unsigned long Cap)
	: Capacity(Cap)
{
	assert_Ns( VarArr_init->size() > Capacity,
			"Ns_ConstrAllDiffStrong::Ns_ConstrAllDiffStrong: Condition required:  VarArr.size() >= 2");
	assert_Ns( Capacity > 0,
			"Ns_ConstrAllDiffStrong::Ns_ConstrAllDiffStrong: Condition required:  Capacity > 0");

	NsIntVarArray::iterator  V = VarArr_init->begin();
	NsProblemManager&  pm = V->manager();

	for ( ;   V != VarArr_init->end();   ++V)   {

		assert_Ns( &pm == &V->manager(),  "Ns_ConstrAllDiffStrong::Ns_ConstrAllDiffStrong: All the variables of a constraint must belong to the same NsProblemManager");

		VarArr.push_back( groupedNsIntVar(*V) );
		VarPointerGroup.insert( make_pair( (Ns_pointer_t)&*V  ,  &VarArr.back() ) );
	}

	//for (X = VarArr->begin();   X != VarArr->end();   ++X)
	//	VarArrGroup.push_back( NsIntVar(pm, NsMINUS_INF+1, NsPLUS_INF-1) );
}



namespace  {

		int
	less_function_MaxMMinSize  (const void *X, const void *Y)
	{
		NsIntVar&  VarX = (*static_cast<Ns_ConstrAllDiffStrong::groupedNsIntVar* const *>( X ))->Var;
		NsIntVar&  VarY = (*static_cast<Ns_ConstrAllDiffStrong::groupedNsIntVar* const *>( Y ))->Var;

		if ( VarX.max()  <  VarY.max()
			|| ( VarX.max() == VarY.max()  &&  ( -VarX.min() < -VarY.min()
					||  ( VarX.min() == VarY.min()  &&  VarX.size()  <  VarY.size() ) ) ) )
		{
			return  -1;
		}

		if ( VarX.max() == VarY.max()  &&  VarX.min() == VarY.min()  &&  VarX.size() == VarY.size() )
			return  0;

		return  +1;
	}





		void
	allDiffBoundsConsistency (NsDeque<Ns_ConstrAllDiffStrong::groupedNsIntVar>& VarArr,
			const unsigned long Capacity,
			const Ns_ConstrAllDiffStrong::groupedNsIntVar::group_t group,
			const Ns_Constraint* constraint)
	{
	//	cout << &VarArr << ": ";
	//	for (NsIndex k=0;   k < VarArr.size();   ++k)
	//		cout << "  " << (VarArr[k].group() - groupedNsIntVar::FIRST_GROUP) << ">" << VarArr[k].Var;
	//	cout << endl;

	//for (groupedNsIntVar::group_t group = groupedNsIntVar::FIRST_GROUP;   /* VOID */ ;   ++group)   {

		//  At first, we gather all the variables with group-id
		//   equal to `group' into the array `VarArrSortedList'.

		NsDeque<Ns_ConstrAllDiffStrong::groupedNsIntVar*>  VarArrSortedList;

		NsIndex  i;

		Ns_ConstrAllDiffStrong::groupedNsIntVar::group_t  nGroups =
			Ns_ConstrAllDiffStrong::groupedNsIntVar::FIRST_GROUP;
		for (i=0;   i < VarArr.size();   ++i)   {

			if ( VarArr[i].group()  ==  group )
				VarArrSortedList.push_back( &VarArr[i] );

			if ( VarArr[i].group()  >   nGroups )
				nGroups = VarArr[i].group();
		}

		assert_Ns( ! VarArrSortedList.empty() ,  "allDiffBoundsConsistency: Empty `group' of variables" );
			//break;	// We have processed all the separate groups of variables.



		//  Copying `VarArrSortedList' to `VarArrSorted' which is friendlier
		//   to the `qsort()' function that it is used bellow.

		Ns_ConstrAllDiffStrong::groupedNsIntVar  **VarArrSorted =
						new Ns_ConstrAllDiffStrong::groupedNsIntVar*[VarArrSortedList.size()];

		for (i=0;  i < VarArrSortedList.size();  ++i)
			VarArrSorted[i] = VarArrSortedList[i];


		//  ... Then we sort the variables in `VarArrSorted', by ascending maximum,
		//   descending minimum, and ascending size.  I.e., if the domain of VarX
		//   is more possible to be a subset of domain of VarY, then VarX precedes
		//   VarY in the array `VarArrSorted'.

		qsort(VarArrSorted, VarArrSortedList.size(), sizeof(Ns_ConstrAllDiffStrong::groupedNsIntVar*),
											less_function_MaxMMinSize);



		//  We gather all the different maxima into the array `Max' by ascending order.

		NsDeque<NsInt>  Max;

		for (i=0;  i < VarArrSortedList.size();  ++i)   {

			if ( i == 0   ||   ( i > 0  &&  VarArrSorted[i]->Var.max() != VarArrSorted[i-1]->Var.max() ) )
				Max.push_back( VarArrSorted[i]->Var.max() );
		}



		NsDeque<Ns_ConstrAllDiffStrong::groupedNsIntVar*>  VarLtMax;
		NsDeque<NsInt>             VarLtMaxMins;

		i = 0;
		for (NsIndex max_i = 0;   max_i < Max.size();   ++max_i)    {

			//  `VarEqMax' consists of all the variables of the
			//   array `VarArr' with `VarArr[i].max() == Max[max_i]'.

			NsDeque<Ns_ConstrAllDiffStrong::groupedNsIntVar*>  VarEqMax;

			for ( ;   i < VarArrSortedList.size()  &&  VarArrSorted[i]->Var.max() == Max[max_i];   ++i)
				VarEqMax.push_back( VarArrSorted[i] );


			//  `VarLeMax' is constructed by merging its previous contents,
			//   represented by `VarLtMax' (initially empty), and `VarEqMax'.
			//   `VarLeMax' contains the constrained variables of `VarArr'
			//   with `VarArr[i].max() <= Max[max_i]'.

			NsDeque<Ns_ConstrAllDiffStrong::groupedNsIntVar*>  VarLeMax;

			NsIndex  i1, i2;

			for (i1=i2=0;  i1 < VarLtMax.size()  &&  i2 < VarEqMax.size();   )     {

				if ( VarLtMax[i1]->Var.min()  >=  VarEqMax[i2]->Var.min() )   {

					VarLeMax.push_back( VarLtMax[i1] );
					++i1;

				} else   {

					VarLeMax.push_back( VarEqMax[i2] );
					++i2;
				}
			}

			//  One of the two arrays (`VarLtMax' and `VarEqMax') is
			//   exhausted, so we append the contents of the other
			//   array to `VarLeMax', and the merging is completed.

			for ( ;   i1 < VarLtMax.size();   ++i1)
				VarLeMax.push_back( VarLtMax[i1] );

			for ( ;   i2 < VarEqMax.size();   ++i2)
				VarLeMax.push_back( VarEqMax[i2] );

			VarLtMax = VarLeMax;	// `VarLtMax' will be used at the next iteration.



			//  `VarLeMaxMins' contains the minima of the constrained variables
			//   included in `VarLeMax', in descending order (without duplicates).
			//   It is constructed by merging the array `VarLtMaxMins' (i.e., the
			//   previous contents of `VarLeMaxMins', that have no duplicates, by
			//   definition) and `VarEqMax'.mins (i.e., the minima of the
			//   constrained variables in `VarEqMax' that may contain duplicates,
			//   so we should avoid them).

			NsDeque<NsInt>  VarLeMaxMins;

			for (i1=i2=0;  i1 < VarLtMaxMins.size()  &&  i2 < VarEqMax.size();   )     {

				if ( VarLtMaxMins[i1]  >  VarEqMax[i2]->Var.min() )   {

					VarLeMaxMins.push_back( VarLtMaxMins[i1] );
					++i1;

				} else if ( VarLtMaxMins[i1]  <  VarEqMax[i2]->Var.min() )   {

					VarLeMaxMins.push_back( VarEqMax[i2]->Var.min() );
					do {
						++i2;	// avoiding duplicates

					} while ( i2 < VarEqMax.size()
							&&  VarEqMax[i2]->Var.min() == VarEqMax[i2-1]->Var.min() );

				} else   {	// The two minima are equal.

					VarLeMaxMins.push_back( VarLtMaxMins[i1] );
					++i1;

					do {
						++i2;	// avoiding duplicates

					} while ( i2 < VarEqMax.size()
							&&  VarEqMax[i2]->Var.min() == VarEqMax[i2-1]->Var.min() );
				}
			}

			//  We complete the merging by appending the contents of the non-
			//   exhausted array (`VarLtMaxMins' or `VarEqMax') to `VarLeMaxMins'.

			for ( ;   i1 < VarLtMaxMins.size();   )     {

				VarLeMaxMins.push_back( VarLtMaxMins[i1] );
				++i1;
			}

			for ( ;   i2 < VarEqMax.size();   )     {

				VarLeMaxMins.push_back( VarEqMax[i2]->Var.min() );
				do {
					++i2;	// avoiding duplicates

				} while ( i2 < VarEqMax.size()
						&&  VarEqMax[i2]->Var.min() == VarEqMax[i2-1]->Var.min() );
			}

			VarLtMaxMins = VarLeMaxMins;	// `VarLtMaxMins' will be used at the next iteration.




			//  `vUnion' is a domain representing the union of the
			//   domains that we have examined so far.  Inintially,
			//   it equals to the domain of `VarLeMax[0]'.

			NsIntVar  *vUnion = new NsIntVar(VarLeMax[0]->Var.manager(), VarLeMax[0]->Var.min(), VarLeMax[0]->Var.max());

			vUnion->manager().removeLastVar();
			// ...because it is temporary;

			NsIntVar::const_gap_iterator  gapVal;

			for (gapVal = VarLeMax[0]->Var.gap_begin();  gapVal != VarLeMax[0]->Var.gap_end();  ++gapVal)   {

				vUnion->remove(*gapVal);

				//assert_Ns( vUnion->removeSingle(*gapVal, constraint),
				//		"Ns_ConstrAllDiffStrong::ArcCons: `vUnion->removeSingle(*gapVal)' failed" );
			}




			//  Iterating through the `VarLeMaxMins', which
			//   has been renamed for readability as `Min'.

			NsDeque<NsInt>  &Min = VarLeMaxMins;

			NsIndex  nVars = 0;
			NsIndex  j = 0;

			for (NsIndex min_i=0;   min_i < Min.size();   ++min_i)   {

				// Iterating through `VarLeMax'...

				for ( ;   j < VarLeMax.size();   ++j)    {

					if ( VarLeMax[j]->Var.min() < Min[min_i] )
						break;	// End of `Min', no propagation.

					++nVars;

					//  We produce the union of the domains `vUnion' and `VarLeMax[j]'.  I.e.,
					//      vUnion  <---  vUnion  UNION  VarLeMax[j].domain.

					NsIntVar  vUnionPrevious = *vUnion;

					delete  vUnion;

					vUnion = new NsIntVar(
							vUnionPrevious.manager(),
							min(vUnionPrevious.min(), VarLeMax[j]->Var.min()),
							max(vUnionPrevious.max(), VarLeMax[j]->Var.max()));

					vUnion->manager().removeLastVar();
					// ...because it is temporary;

					//  Removing the values that neither domain contains.

					for (gapVal = vUnionPrevious.gap_begin();
							gapVal != vUnionPrevious.gap_end();
							++gapVal)
					{
						if ( ! VarLeMax[j]->Var.contains( *gapVal ) )   {
							vUnion->remove(*gapVal);
							//assert_Ns( vUnion->removeSingle(*gapVal,constraint),  "Ns_ConstrAllDiffStrong::ArcCons: `vUnion->removeSingle(*gapVal)' failed" );
						}
					}

					for (gapVal = VarLeMax[j]->Var.gap_begin();
							gapVal != VarLeMax[j]->Var.gap_end();
							++gapVal)
					{
						if ( ! vUnionPrevious.contains( *gapVal ) )
						{
							vUnion->remove(*gapVal);
							//assert_Ns( vUnion->Single(*gapVal,constraint),  "Ns_ConstrAllDiffStrong::ArcCons: `vUnion->removeSingle(*gapVal)' failed" );
						}
					}




					NsIndex  sizeXcap  =  vUnion->size() * Capacity;

					if ( sizeXcap  <  nVars )    {

						//  The number of the variables is too big to take
						//   `sizeXcap' different values.   ==>   Failure

						VarLeMax[0]->Var.removeAll();

						delete  vUnion;
						delete  []  VarArrSorted;

						return;
					}


					if ( sizeXcap  ==  nVars
							&&  ( j < VarLeMax.size()-1  ||  i < VarArrSortedList.size() ) )
					{

						//  The number of the variables is the minimum needed to take
						//   `sizeXcap' different values (contained in `vUnion').
						//   Each variable has to be assigned a value from `vUnion', and
						//   all the values will be used.  So no other variable should be
						//   assigned a value from `vUnion'.  Thus, it is possible to
						//   subtract this domain from all the other variables, and to
						//   separate them from the current group, by changing their group.
						//   (This domain is in other words a `Hall Interval'.)

						++nGroups;

//						bool changed=false;
						for (++j;  j < VarLeMax.size();  ++j)   {
//							changed = true;

							if ( ! VarLeMax[j]->removeDomain(*vUnion, constraint) )    {

								delete  vUnion;
								delete  []  VarArrSorted;

								return;
							}

							VarLeMax[j]->setGroup( nGroups );
						}

						for ( ;  i < VarArrSortedList.size();  ++i)   {
//							changed = true;

							if ( ! VarArrSorted[i]->removeDomain(*vUnion, constraint) )    {

								delete  vUnion;
								delete  []  VarArrSorted;

								return;
							}

							VarArrSorted[i]->setGroup( nGroups );
						}

						allDiffBoundsConsistency(VarArr, Capacity, nGroups, constraint);

						max_i = Max.size();

//						if ( changed )   {
//	cout << "           ";
//	for (NsIndex k=0;   k < VarArr.size();   ++k)
//		cout << "  " << (VarArr[k].group() - groupedNsIntVar::FIRST_GROUP) << ">" << VarArr[k].Var;
//	cout << endl;
//						}
					}


					if ( sizeXcap  >  VarLeMax.size() )    {

						//  The number of the values `sizeXcap' to be assigned to be assigned
						//   to different variables of the array `VarLeMax' is already greater
						//   than the minimum needed, so there is no need to examine the rest
						//   of the variables of `VarLeMax'.  Thus, we override them (`early
						//   cut-off') using the following statements.

						min_i = Min.size();
						break;
					}

				}
			}

			delete  vUnion;

		}

		delete  []  VarArrSorted;

	//} // groups iteration
	}

} // namespace





// bounds-consistency only
	void
Ns_ConstrAllDiffStrong::ArcCons (void)
{
	allDiffBoundsConsistency(VarArr, Capacity, groupedNsIntVar::FIRST_GROUP, this);
}


// bounds-consistency only
	void
Ns_ConstrAllDiffStrong::LocalArcCons (Ns_QueueItem& Qitem)
{
	//if (Qitem.getVarFired()->min() < Qitem.getW()  &&  Qitem.getW() < Qitem.getVarFired()->max())
	//	return;	// bounds-consistency does not care

	VarPointerGroup_t::const_iterator  cit = VarPointerGroup.find( (Ns_pointer_t)Qitem.getVarFired() );
	groupedNsIntVar::group_t  groupFired = cit->second->group();

	//ArcCons();
	allDiffBoundsConsistency(VarArr, Capacity, groupFired, this);
}










namespace  {

		void
	countUpdateMinMax (NsIntVar& vMinValueIndex,
			NsIntVar& vMaxValueIndex,
			NsIntVarArray& vCount)
	{
		NsInt  i;


		for (i=vMinValueIndex.min();  i < static_cast<NsInt>(vCount.size());  ++i)    {

			if ( vCount[i].max() != 0 )
				break;
		}

		vMinValueIndex.remove(NsMINUS_INF, i-1);


		for (i=vMaxValueIndex.max();  i >= 0;  --i)    {

			if ( vCount[i].max() != 0 )
				break;
		}

		vMaxValueIndex.remove(i+1, NsPLUS_INF);
	}

} // namespace



Ns_ConstrCount::Ns_ConstrCount (NsIntVarArray *VarArr_init,
				const NsDeque<NsInt>& Values,
				const NsDeque<NsInt>& Occurrences)
	: VarArr(VarArr_init)
	  //Values(Values_init), Occurrences(Occurrences_init)
{
	NsProblemManager  *pm=0;

	NsIntVarArray::iterator  X = VarArr->begin();
	if ( X  !=  VarArr->end() )   {
		pm  =  &X->manager();
		++X;

		vMinValueIndex = NsIntVar(*pm,0,Values.size());
		vMaxValueIndex = NsIntVar(*pm,-1,Values.size()-1);
		//  vMinValueIndex and vMaxValueIndex domains are
		//   respectively shifted left and right by 1, in
		//   order to avoid provoking an inconsistency
		//   when all the values have been assigned.
	}

	for ( ;   X != VarArr->end();   ++X)  {
		assert_Ns( pm == &X->manager(),  "Ns_ConstrCount::Ns_ConstrCount: All the variables of a constraint must belong to the same NsProblemManager");
	}

	assert_Ns( Values.size() == Occurrences.size() ,
	"Ns_ConstrCount::Ns_ConstrCount: `Values' and `Occurrences' sizes should match");


	//  Sort tuple <Value,Occurrence> by value.
	//NsDeque<ValueOccurrence_t>  ValuesOccurrences;
	NsIndex  occurrencesSum = 0;
	NsIndex  i;
	for (i=0;  i < Values.size();  ++i)   {

		ValuesOccurrences.push_back(
			ValueOccurrence_t(Values[i],Occurrences[i]) );

		occurrencesSum  +=  Occurrences[i];
	}
	sort(ValuesOccurrences.begin(), ValuesOccurrences.end());

	assert_Ns( occurrencesSum == VarArr->size() ,
	"Ns_ConstrCount::Ns_ConstrCount: `Occurrences' sum does not match `VarArr' size");


	for (i=0;  i < Values.size();  ++i)  {

		assert_Ns( ValueIndex.count( ValuesOccurrences[i].value ) == 0,
			"Ns_ConstrCount::Ns_ConstrCount: Duplicate value");

		ValueIndex.insert( make_pair( ValuesOccurrences[i].value , i ) );

		vCount.push_back( NsIntVar(*pm, 0, ValuesOccurrences[i].occurrence) );
	}

	countUpdateMinMax(vMinValueIndex, vMaxValueIndex, vCount);
}



namespace  {

	//	void
	//countReviseValue (NsIntVar& Var, const NsInt value,
	//		NsIntVarArray& vCount,
	//		const Ns_ConstrCount::ValueIndex_t& ValueIndex,
	//		const Ns_Constraint *constraint)
	//{
	//	Ns_ConstrCount::ValueIndex_t::const_iterator  cit =
	//		ValueIndex.find( value );

	//	if ( cit == ValueIndex.end() ||
	//			vCount[cit->second].max() == 0 )
	//	{
	//		Var.removeSingle(value, constraint);
	//	}
	//}


		void
	countArcCons (NsIntVar& Var,
		NsIntVarArray& vCount,
		NsIntVar& vMinValueIndex,
		NsIntVar& vMaxValueIndex,
		const Ns_ConstrCount::ValueIndex_t& ValueIndex,
		const NsDeque<Ns_ConstrCount::ValueOccurrence_t>& ValuesOccurrences,
		const Ns_Constraint *constraint)
	{
		//for (NsIntVar::const_iterator val=Var.begin();
		//		val != Var.end();
		//		++val)
		//{
		//	countReviseValue(Var, *val, vCount, ValueIndex, constraint);
		//}




		//NsInt  value;

		//do  {
		//	value  =  Var.min();

		//	countReviseValue(Var, value, vCount, ValueIndex, constraint);

		//} while ( Var.min()  !=  value );

		//do  {
		//	value  =  Var.max();

		//	countReviseValue(Var, value, vCount, ValueIndex, constraint);

		//} while ( Var.max()  !=  value );



		if ( vMinValueIndex.min()-1  >=  0 )   {

			Var.removeRange(NsMINUS_INF,
			ValuesOccurrences[vMinValueIndex.min()-1].value,
			constraint);
		}

		if ( static_cast<NsIndex>(vMaxValueIndex.max()+1) <
				ValuesOccurrences.size() )
		{

			Var.removeRange(ValuesOccurrences[vMaxValueIndex.max()+1].value,
			NsPLUS_INF, constraint);
		}



		if ( Var.isBound() )    {

			Ns_ConstrCount::ValueIndex_t::const_iterator  cit =
				ValueIndex.find( Var.value() );

			if ( cit  ==  ValueIndex.end() )    {
				vCount[0].removeAll();
				return;
			}

			NsIndex  index = cit->second;
			vCount[index].remove( vCount[index].max() );

			if ( vCount[index].max()  ==  0 )   {

				countUpdateMinMax(vMinValueIndex,
						vMaxValueIndex, vCount);
			}
		}
	}

} // namespace



	void
Ns_ConstrCount::ArcCons (void)
{
	for (NsIntVarArray::iterator X=VarArr->begin();
			X != VarArr->end();
			++X)
	{
		countArcCons(*X, vCount, vMinValueIndex, vMaxValueIndex,
				ValueIndex, ValuesOccurrences, this);
	}
}


	void
Ns_ConstrCount::LocalArcCons (Ns_QueueItem& Qitem)
{
	countArcCons(*Qitem.getVarFired(), vCount, vMinValueIndex,
		vMaxValueIndex, ValueIndex, ValuesOccurrences, this);
}







//namespace  {
//		void
//	MakeIDs (NsIntVarArray *VarArr)
//	{
//		NsIntVarArray::iterator  X;
//
//		if ( X->IsSetID() )   {
//			X = VarArr->begin();
//			NsIndex  previous = X->getID();
//			++X;
//
//			for ( ;   X != VarArr->end();   ++X)   {
//				assert_Ns( X->getID() == previous + 1 ,  "MakeIDs: Non-continuous ids in `VarArr'");
//				previous = X->getID();
//			}
//
//		}  else  {
//			for (X=VarArr->begin();   X != VarArr->end();   ++X)
//				X->setID();
//		}
//	}
//}  // namespace









Ns_ConstrInverse::Ns_ConstrInverse (NsIntVarArray *VarArrInv_init, NsIntVarArray *VarArr_init)
	: VarArrInv(VarArrInv_init),  VarArr(VarArr_init), VArrInv(*VarArrInv), VArr(*VarArr)
{
	revisionType  =  VALUE_CONSISTENCY;


	assert_Ns( ! VarArrInv->empty()  &&  ! VarArr->empty() ,
			"Ns_ConstrInverse::Ns_ConstrInverse: Condition required:  Both arrays must have some elements");

	NsIntVarArray::iterator  X = VarArr->begin();
	NsProblemManager&  pm = X->manager();
	++X;
	for ( ;   X != VarArr->end();   ++X)   {
		assert_Ns( &pm == &X->manager(),  "Ns_ConstrInverse::Ns_ConstrInverse: All the variables of a constraint must belong to the same NsProblemManager");
	}
	for (X = VarArrInv->begin();   X != VarArrInv->end();   ++X)  {
		assert_Ns( &pm == &X->manager(),  "Ns_ConstrInverse::Ns_ConstrInverse: All the variables of a constraint must belong to the same NsProblemManager");
	}

	NsIndex  i;
	for (X=VarArr->begin(), i=0;   X != VarArr->end();   ++X, ++i)   {
		assert_Ns( VarArrayIndex.count( (Ns_pointer_t)&*X ) == 0,
				"Ns_ConstrInverse::Ns_ConstrInverse: Duplicate NsIntVar");
		VarArrayIndex.insert( make_pair( (Ns_pointer_t)&*X  ,  ArrayIndex_t( false , i ) ) );
	}
	for (X=VarArrInv->begin(), i=0;   X != VarArrInv->end();   ++X, ++i)   {
		assert_Ns( VarArrayIndex.count( (Ns_pointer_t)&*X ) == 0,
				"Ns_ConstrInverse::Ns_ConstrInverse: Duplicate NsIntVar");
		VarArrayIndex.insert( make_pair( (Ns_pointer_t)&*X  ,  ArrayIndex_t( true , i ) ) );
	}
	//MakeIDs(VarArr);
	//MakeIDs(VarArrInv);
}


	void
Ns_ConstrInverse::ArcCons (void)
{
	NsIndex  i;
	NsIntVar::const_iterator  val;

	for (i = 0;   i < VArrInv.size();   ++i)   {
		for (val = VArrInv[i].begin();  val != VArrInv[i].end();   ++val)  {
		    if (*val != -1)   {
			if ( *val < -1  ||  static_cast<unsigned>(*val) >= VArr.size()  ||  ! VArr[*val].contains(i) )
				VArrInv[i].removeSingle( *val , this);
			else if ( VArr[*val].isBound() )
				VArrInv[i].removeSingle( -1 , this);
		    }
		}
	}

	for (i = 0;   i < VArr.size();   ++i)   {
		for (val = VArr[i].begin();  val != VArr[i].end();   ++val)  {
			if ( *val < 0  ||  static_cast<unsigned>(*val) >= VArrInv.size()  ||  ! VArrInv[*val].contains(i) )
				VArr[i].removeSingle( *val , this);
		}
	}
}


	void
Ns_ConstrInverse::LocalArcCons (Ns_QueueItem& Qitem)
{
	NsInt  VarFiredW = Qitem.getW();
	if  (VarFiredW < 0)
		return;
	VarArrayIndex_t::const_iterator  cit = VarArrayIndex.find( (Ns_pointer_t)Qitem.getVarFired() );
	NsIndex  VarFiredId = cit->second.index;


	if ( cit->second.InInverse )   {

		if (static_cast<unsigned>(VarFiredW) >= VArr.size())
			return;
		//if ( VArr[VarFiredW].contains(VarFiredId) )
		VArr[VarFiredW].removeSingle( VarFiredId , this);

	}  else  {

		if ( Qitem.getVarFired()->isBound() )   {
			NsInt  val = Qitem.getVarFired()->value();
			assert_Ns( 0<=val && static_cast<unsigned>(val) < VArrInv.size() ,
				"Ns_ConstrInverse::LocalArcCons: `val' out of range");
			//if ( VArrInv[val].contains(-1) )
			VArrInv[val].removeSingle( -1 , this);
		}

		if (static_cast<unsigned>(VarFiredW) >= VArrInv.size())
			return;
		//if ( VArrInv[VarFiredW].contains(VarFiredId) )
		VArrInv[VarFiredW].removeSingle( VarFiredId , this);
	}
}









	void
Ns_ConstrElement::ArcCons (void)
{
	if ( ! VarIndex->removeRange(NsMINUS_INF, -1, this)
	    || ! VarIndex->removeRange(intArray.size(), NsPLUS_INF, this) )
	{
		return;
	}

	NsIntVar::const_iterator  index, val;

	for (index = VarIndex->begin();
			index != VarIndex->end();
			++index)
	{
		if ( ! VarValue->contains( intArray[*index] ) )
			VarIndex->removeSingle(*index, this);
	}

	for (val = VarValue->begin();  val != VarValue->end();  ++val)    {

		for (index = VarIndex->begin();
				index != VarIndex->end();
				++index)
		{
			if ( intArray[*index]  ==  *val )
				break;
		}

		if ( index  ==  VarIndex->end() )
			VarValue->removeSingle(*val, this);
	}
}


	void
Ns_ConstrElement::LocalArcCons (Ns_QueueItem& Qitem)
{
	NsIntVar::const_iterator  index;


	if ( VarIndex  ==  Qitem.getVarFired() )    {

		if ( 0 <= Qitem.getW()
				&&  static_cast<NsIndex>(Qitem.getW()) < intArray.size() )
		{
			NsInt  SupportVal = intArray[Qitem.getW()];

			for (index = VarIndex->begin();
					index != VarIndex->end();
					++index)
			{
				if ( intArray[*index]  ==  SupportVal )
					break;
			}

			if ( index  ==  VarIndex->end() )
				VarValue->removeSingle(SupportVal, this);
		}

	}  else  {
		assert_Ns( VarValue == Qitem.getVarFired() ,
		"Ns_ConstrElement::LocalArcCons: Wrong getVarFired");

		for (index = VarIndex->begin();
				index != VarIndex->end();
				++index)
		{
			if ( intArray[*index]  ==  Qitem.getW() )
				VarIndex->removeSingle(*index, this);
		}
	}
}










///  @{
///  \name  Representation of higher order constraints in a graph


///  Auxiliary function to depict a ternary constraint into a graph file.

	void
naxos::Ns_ternaryConstraintToGraphFile (
		ofstream& fileConstraintsGraph,
		const NsIntVar *VarX,
		const NsIntVar *VarY,
		const NsIntVar *VarZ,
		const Ns_Constraint *constr,
		const char *constrName,
		const bool sourceLabels)
{
	fileConstraintsGraph
		<< "\n\tConstr" << constr
		<< "  [shape=point];\n"
		<< "\tVar" << VarY << "    -> Constr" << constr
		<< "   [arrowhead=none"
		<< ( ( sourceLabels ) ? ", headlabel=\"y\"" : "" )
		<< "];\n"
		<< "\tVar" << VarZ << "    -> Constr" << constr
		<< "   [arrowhead=none"
		<< ( ( sourceLabels ) ? ", headlabel=\"z\"" : "" )
		<< "];\n"
		<< "\tConstr" << constr << " -> Var" << VarX << "   "
		<< "   [taillabel=\"" << constrName << "\"];\n";
}




///  Auxiliary function to depict a global constraint into a graph file.

	void
naxos::Ns_globalConstraintToGraphFile (
		ofstream& fileConstraintsGraph,
		const NsIntVar *VarX,
		const NsIntVarArray *VarArr,
		const Ns_Constraint *constr,
		const char *constrName)
{
	fileConstraintsGraph
		<< "\n\tConstr" << constr
		<< "  [shape=point];\n";


	for (NsIntVarArray::const_iterator  V = VarArr->begin();
			V  !=  VarArr->end();
			++V)
	{
		fileConstraintsGraph << "\tVar"
			<< &*V << "    -> Constr" << constr
			<< "   [arrowhead=none, style=dotted];\n";
	}


	fileConstraintsGraph << "\tConstr"
		<< constr << " -> Var" << VarX << "   "
		<< "   [taillabel=\"" << constrName
		<< "\", style=dotted];\n";
}




///  Auxiliary function to depict an array-constraint into a graph file.

	void
naxos::Ns_arrayConstraintToGraphFile (
		ofstream& fileConstraintsGraph,
		const NsIntVarArray *VarArr,
		const Ns_Constraint *constr,
		const char *constrName)
{
	fileConstraintsGraph
		<< "\n\tConstr" << constr
		<< "  [shape=point];\n";

	NsIntVarArray::const_iterator  V = VarArr->begin();

	fileConstraintsGraph << "\tVar"
		<< &*V << " -> Constr" << constr
		<< "   [arrowhead=none, style=dotted, headlabel=\""
		<< constrName <<"\"];\n";

	++V;

	for ( ;   V != VarArr->end();   ++V)    {

		fileConstraintsGraph << "\tVar"
			<< &*V << " -> Constr" << constr
			<< "   [arrowhead=none, style=dotted];\n";
	}
}




///  Auxiliary function to depict an Inverse constraint into a graph file.

	void
naxos::Ns_inverseConstraintToGraphFile (
		ofstream& fileConstraintsGraph,
		const NsIntVarArray *VarArr,
		const NsIntVarArray *VarArrInv,
		const Ns_Constraint *constr)
{
	fileConstraintsGraph
		<< "\n\tConstr" << constr
		<< "  [shape=point];\n";

	NsIndex  i = 0;

	fileConstraintsGraph << "\tConstr"
		<< constr << " -> Var" << &(*VarArr)[i]
		<< "   [arrowhead=odot, style=dotted, headlabel=\""
		<< i << "\", taillabel=\"Inverse\"];\n";

	++i;

	for ( ;   i < VarArr->size();   ++i)    {

		fileConstraintsGraph << "\tConstr"
		<< constr << " -> Var" << &(*VarArr)[i]
		<< "   [arrowhead=odot, style=dotted, headlabel=\""
		<< i << "\"];\n";
	}

	for (i=0;   i < VarArrInv->size();   ++i)    {

		fileConstraintsGraph << "\tConstr"
		<< constr << " -> Var" << &(*VarArrInv)[i]
		<< "   [arrowhead=dot, style=dotted, headlabel=\""
		<< i << "\"];\n";
	}
}


///  @}
