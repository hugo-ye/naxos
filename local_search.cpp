///  \file
///  \brief  Local Search propagation engine implementation.
///
///  \internal
///  This file is part of
///   <span style="font-variant: small-caps;"> Naxos Solver: </span>
///   A Constraint Programming Library. \n
///   Copyright © 2007-2010  Nikolaos Pothitos.
///
///  See ../license/LICENSE for the license of the library.





#include "naxos.h"
#include <algorithm>


using namespace naxos;








///  Deletes all the references to this variable caused by the current assignment.

	void
NsIntVar::lsDeleteAssignmentDependencies (void)
{
	assert_Ns( lsIsBound() ,
	"NsIntVar::lsDeleteAssignmentDependencies: `*this': Not a bound NsIntVar" );

	if ( lsIsIntermediate() )    {

		assert_Ns( lsSupportTuples.empty()
			&& lsPointersToSupportTuples.empty()
			&& lsViolatedConstrs.empty()
			&& lsPointersToTuples.empty() ,
			"NsIntVar::lsDeleteAssignmentDependencies: Bad intermediate variable state" );

	}  else  {

		lsDeleteSupportTuples();
	}


	//for (NsList< NsList<VarPointer_t> >::iterator
	//		tuple=lsSupportTuples.begin();
	//		tuple != lsSupportTuples.end();
	//		tuple = lsSupportTuples.erase(tuple))
	//{
	//	for (NsList<VarPointer_t>::iterator
	//			var_pointer=tuple->begin();
	//			var_pointer != tuple->end();
	//			var_pointer = tuple->erase(var_pointer))
	//	{
	//		var_pointer->Var->lsPointersToSupportTuples.erase(
	//			var_pointer->pointerToPointersToSupportTuples);
	//	}
	//}

	//for (NsList<VarPointerToPointer_t>::iterator
	//		var_pointer=lsPointersToSupportTuples.begin();
	//		var_pointer != lsPointersToSupportTuples.end();
	//		var_pointer = lsPointersToSupportTuples.erase(var_pointer))
	//{
	//	var_pointer->Var->lsSupportTuples.erase(
	//		var_pointer->pointerToSupportTuples);

	//	if ( var_pointer->Var->lsSupportTuples.empty()
	//		&& var_pointer->Var->lsIsIntermediate() )
	//			var_pointer->Var->lsUnsetCommit();
	//}

	if ( ! lsViolatedConstrs.empty() )
		manager().lsConflictingVariables.erase(lsPointerToConflictingVariablesItem);


	NsList< NsList<LsPointersToTuples_t>::iterator >::iterator
		auxTuple = lsPointersToTuples.begin();

	for (NsList< NsList<NsIntVar*> >::iterator
			tuple=lsViolatedConstrs.begin();
			tuple != lsViolatedConstrs.end();
			tuple = lsViolatedConstrs.erase(tuple),
			auxTuple = lsPointersToTuples.erase(auxTuple))
	{
		NsList<LsPointersToTuples_t::LsPointersToTuplesOfVar_t>::iterator
			V_list_items = (*auxTuple)->tuple.begin();

		for (NsList<NsIntVar*>::iterator
			V=tuple->begin();
			V != tuple->end();
			V = tuple->erase(V),
			V_list_items = (*auxTuple)->tuple.erase(V_list_items))
		{
			if ( *V  !=  this )    {

				(*V)->lsViolatedConstrs.erase(
						V_list_items->varsListItem );

				(*V)->lsPointersToTuples.erase(
						V_list_items->pointersListItem );

				if ( (*V)->lsViolatedConstrs.empty() )    {

					(*V)->manager().lsConflictingVariables.erase((*V)->lsPointerToConflictingVariablesItem);
				}
			}
		}

		assert_Ns( V_list_items == (*auxTuple)->tuple.end() ,
			"NsIntVar::lsDeleteAssignmentDependencies: Lists `tuple' and `auxTuple' have not the same length" );

		manager().lsViolatedConstrs.erase( (*auxTuple)->varsListItem );

		manager().lsPointersToTuples.erase( *auxTuple );
	}

	assert_Ns( auxTuple == lsPointersToTuples.end() ,
		"NsIntVar::lsDeleteAssignmentDependencies: Lists `lsViolatedConstrs' and `lsPointersToTuples' have not the same length" );


	//lsViolatedConstrsIDs.clear();
}





///  Recursively deletes every support to intermediate variables.

	void
NsIntVar::lsDeleteSupportTuples (void)
{
	for (NsList<VarPointerToPointer_t>::iterator
			var_pointer=lsPointersToSupportTuples.begin();
			var_pointer != lsPointersToSupportTuples.end();
			var_pointer = lsPointersToSupportTuples.erase(var_pointer))
	{
		assert_Ns( var_pointer->Var->lsIsIntermediate() ,
		"NsIntVar::lsDeleteSupportTuples: `var_pointer->Var' is not intermediate" );

		var_pointer->Var->lsDeleteSupportTuples();

		var_pointer->Var->lsSupportTuples.erase(
			var_pointer->pointerToSupportTuples);

		if ( var_pointer->Var->lsSupportTuples.empty() )
			var_pointer->Var->lsUnset();
	}
}





///  Undo the assignment of the variable.

	void
NsIntVar::lsUnset (void)
{
	//assert_Ns( ! lsIsIntermediate() ,
	//	"NsIntVar::lsUnset: Variable is intermediate" );

	assert_Ns( lsIsBound() ,
		"NsIntVar::lsUnset: Variable already unassigned" );

	//manager().lsUnassignQueue.push_back( this );

	lsDeleteAssignmentDependencies();

	lsVal  =  NsMINUS_INF;
}





/////  Permanently un-assign variable.
//
//	void
//NsIntVar::lsUnsetCommit (void)
//{
//	//if ( ! lsIsIntermediate() )
//	lsDeleteAssignmentDependencies();
//
//	lsVal  =  NsMINUS_INF;
//}




///  Recursively retrieves the non-intermediate variables whose assignments support this assignment.

	void
NsIntVar::findSupporters (NsList< NsList<NsIntVar*> >& supportNonIntrmdtTuples)
{
	assert_Ns( lsIsBound() , "NsIntVar::findSupporters: Unbound `*this'" );

	for (NsList< NsList<VarPointer_t> >::iterator
			tuple=lsSupportTuples.begin();
			tuple != lsSupportTuples.end();
			++tuple)
	{
		assert_Ns( lsIsIntermediate() ,
			"NsIntVar::findSupporters: Bad supporters state" );

		NsList< NsList<NsIntVar*> >  supportForTuple;
		supportForTuple.push_back( NsList<NsIntVar*>() );

		for (NsList<VarPointer_t>::iterator
				var_pointer=tuple->begin();
				var_pointer != tuple->end();
				++var_pointer)
		{
			NsList< NsList<NsIntVar*> >  supportForVar;
			supportForVar.push_back( NsList<NsIntVar*>() );
			var_pointer->Var->findSupporters(supportForVar);

			NsList< NsList<NsIntVar*> >  supportForTupleNew;

			for (NsList< NsList<NsIntVar*> >::iterator
					tuple1=supportForTuple.begin();
					tuple1 != supportForTuple.end();
					++tuple1)
			{
				for (NsList< NsList<NsIntVar*> >::iterator
						tuple2=supportForVar.begin();
						tuple2 != supportForVar.end();
						++tuple2)
				{
					supportForTupleNew.push_back(
						*tuple1 );

					for (NsList<NsIntVar*>::iterator
						V=tuple2->begin();
						V != tuple2->end();
						++V)
					{
						if ( find(tuple1->begin(),
							tuple1->end(),*V)
							== tuple1->end() )
						{
							supportForTupleNew.back().push_back( *V );
						}
					}
				}
			}

			supportForTuple  =  supportForTupleNew;
		}

		NsList< NsList<NsIntVar*> >  supportTuplesNew;

		for (NsList< NsList<NsIntVar*> >::iterator
				tuple1=supportNonIntrmdtTuples.begin();
				tuple1 != supportNonIntrmdtTuples.end();
				++tuple1)
		{
			for (NsList< NsList<NsIntVar*> >::iterator
					tuple2=supportForTuple.begin();
					tuple2 != supportForTuple.end();
					++tuple2)
			{
				supportTuplesNew.push_back(
					*tuple1 );

				for (NsList<NsIntVar*>::iterator
					V=tuple2->begin();
					V != tuple2->end();
					++V)
				{
					if ( find(tuple1->begin(),
						tuple1->end(),*V)
						== tuple1->end() )
					{
						supportTuplesNew.back().push_back( *V );
					}
				}
				//count(tuple2->begin(), tuple2->end(), this);
			}
		}

		supportNonIntrmdtTuples  =  supportTuplesNew;
	}


	if ( ! lsIsIntermediate() )    {

		assert_Ns( lsSupportTuples.empty() ,
			"NsIntVar::findSupporters: Bad supporters state" );

		for (NsList< NsList<NsIntVar*> >::iterator
				tuple1=supportNonIntrmdtTuples.begin();
				tuple1 != supportNonIntrmdtTuples.end();
				++tuple1)
		{
			tuple1->push_back( this );
		}
	}
}





///  Assign a value to the variable.

	void
NsIntVar::lsSet (const NsInt val,
		const NsList<NsIntVar*> supportTuple,
		const Ns_Constraint *constrFired)
{
	//assert_Ns( ! lsIsIntermediate() ,
	//	"NsIntVar::lsSet: Variable is intermediate" );

	if ( lsIsBound()  &&  supportTuple.empty() )    {

		assert_Ns( lsValue()  !=  val ,
			"NsIntVar::lsSet: Already set at the same value" );

		lsUnset();
		//manager().lsUnassignQueue.push_back( this );
	}

//	manager().lsAssignQueue.push_back( NsProblemManager::VarValue_t(this,val) );
//}
//
//
//
//
/////  Permanently assign a value to the variable.
//
//	void
//NsIntVar::lsSetCommit (const NsInt val,
//		const NsList<NsIntVar*> supportTuple,
//		const Ns_Constraint *constrFired)
//{

	if ( lsIsBound() )    {

		assert_Ns( ! ( lsIsIntermediate() && lsSupportTuples.empty() ) ,
			"NsIntVar::lsSet: Empty support tuples" );

		assert_Ns( ! supportTuple.empty() ,
			"NsIntVar::lsSet: Empty `supportTuple'" );

		if ( lsVal  !=  val )    {

			//  There is a violated constraint.

			NsList< NsList<NsIntVar*> >  conflictNonIntrmdtTuples;
			conflictNonIntrmdtTuples.push_back( NsList<NsIntVar*>() );
			findSupporters(conflictNonIntrmdtTuples);

			for (NsList<NsIntVar*>::const_iterator
				V=supportTuple.begin();
				V != supportTuple.end();
				++V)
			{
				(*V)->findSupporters(conflictNonIntrmdtTuples);
			}

			for (NsList< NsList<NsIntVar*> >::const_iterator
				tuple=conflictNonIntrmdtTuples.begin();
				tuple != conflictNonIntrmdtTuples.end();
				++tuple)
			{
				manager().lsViolatedConstrs.push_back( *tuple );

				manager().lsPointersToTuples.push_back(
					NsIntVar::LsPointersToTuples_t() );
				manager().lsPointersToTuples.back().varsListItem
					=  --manager().lsViolatedConstrs.end();

				for (NsList<NsIntVar*>::const_iterator
					V=tuple->begin();
					V != tuple->end();
					++V)
				{
					if ( (*V)->lsViolatedConstrs.empty() )    {

						(*V)->manager().lsConflictingVariables.push_back( *V );
						(*V)->lsPointerToConflictingVariablesItem  =
							--(*V)->manager().lsConflictingVariables.end();
					}

					(*V)->lsViolatedConstrs.push_back( *tuple );
					(*V)->lsPointersToTuples.push_back( --manager().lsPointersToTuples.end() );

					manager().lsPointersToTuples.back().tuple.push_back(
						LsPointersToTuples_t::
						LsPointersToTuplesOfVar_t(
						--(*V)->lsViolatedConstrs.end(),
						--(*V)->lsPointersToTuples.end()) );


					//for (NsList<VarPointer_t>::iterator
					//		var_pointer=tuple->begin();
					//		var_pointer != tuple->end();
					//		++var_pointer)
					//{
					//	lsViolatedConstrs.back().push_back(
					//			var_pointer->Var );
					//}
				}
			}
			return;
		}

		if ( ! lsIsIntermediate() )
			return;

	}  else  {

		assert_Ns( lsSupportTuples.empty() ,
			"NsIntVar::lsSet: Non-empty support tuples" );

		assert_Ns( ! ( lsIsIntermediate() && supportTuple.empty() ) ,
			"NsIntVar::lsSet: Empty `supportTuple'" );

		if ( ! lsIsIntermediate()  &&  ! supportTuple.empty() )
			return;		// may change in future

		assert_Ns( contains(val) ,
			"NsIntVar::lsSet: Value is out of domain" );

		lsVal  =  val;
	}

	//  Update the support tuples.
	if ( ! supportTuple.empty() )    {

		lsSupportTuples.push_back( NsList<VarPointer_t>() );

		for (NsList<NsIntVar*>::const_iterator
				V=supportTuple.begin();
				V != supportTuple.end();
				++V)
		{
			(*V)->lsPointersToSupportTuples.push_back(
					VarPointerToPointer_t(this) );
			lsSupportTuples.back().push_back( VarPointer_t(*V) );
		}
	}

	//manager().lsQueue.push( NsProblemManager::LsQueueItem_t(this,constrFired) );

	for (NsDeque<ConstraintAndFailure>::const_iterator
			c=constraints.begin();
			c != constraints.end();
			++c)
	{
		if ( c->constr  !=  constrFired )
			c->constr->lsFixedCons(this);
	}
}





/////  Propagates the effects of the (un)assignments via constraints.
//
//	void
//NsProblemManager::lsPropagate (void)
//{
//}




	//ex-lsSet...
	//
	//for (NsList< NsList<NsIntVar*> >::const_iterator c=manager().lsViolatedConstraints().begin();  c != manager().lsViolatedConstraints().end();  ++c)
	//	for (NsList<NsIntVar*>::const_iterator V=c->begin();  V != c->end();  ++V)
	//		(*V)->lsNotIntermediate(1);

	//for (NsList<NsIntVar*>::const_iterator V=manager().lsConflictingVars().begin();  V != manager().lsConflictingVars().end();  ++V)
	//	(*V)->lsNotIntermediate(1);

	//NsIntVar  Y;

	//for (NsList< NsList<NsIntVar*> >::const_iterator c=Y.lsViolatedConstraints().begin();  c != Y.lsViolatedConstraints().end();  ++c)
	//	for (NsList<NsIntVar*>::const_iterator V=c->begin();  V != c->end();  ++V)
	//		(*V)->lsNotIntermediate(1);


	//TODO: delete all violated constraints

	//assert_Ns( supportTuple.empty()  ==  ( constrFired == 0 ) ,
	//	"NsIntVar::lsSetCommit: `supportTuple' or `constrFired' is not provided" );

	//if ( lsIsIntermediate() )    {

	//	assert_Ns( ! supportTuple.empty() ,
	//		"NsIntVar::lsSetCommit: Direct assignment to an intermediate variable" );

	//}  else  {


	//	lsSupportTuples.clear();

	//	lsSupportTuples.push_back( supportTuple );
	//	lsSupportTuples.back().push_back( VarVal_t(this,val) );

	//	for (list<VarVal_t>::const_iterator var_val=lsSupportTuples.back().begin();
	//			var_val->Var != this;
	//			++var_val)
	//	{
	//		var_val->Var->lsSupportTuples.push_back( lsSupportTuples.back() );
	//	}
	//}

	//manager().lsQueue.push(
	//	NsProblemManager::LsQueueItem_t(this, constrFired) );

	//if ( ! lsIsIntermediate() )    {

	//	if ( constrFired == 0 )    {
	//		manager().lsQueue.push( NsProblemManager::LsQueueItem_t(this,constrFired) );
	//	}  else  {
	//		// *Push* nothing; this behaviour may change in the future.
	//		return;
	//	}
	//}





	void
Ns_ConstrXeqYplusC::lsFixedCons (NsIntVar* varFired)
{
	assert_Ns( varFired->lsIsBound() ,
		"Ns_ConstrXeqYplusC::lsFixedCons: Unbound `varFired'" );

	if ( VarX  ==  varFired )    {

		VarY->lsSet(VarX->lsValue()-C, NsList<NsIntVar*>(VarX), this);

	}  else  {

		assert_Ns( VarY == varFired ,
			"Ns_ConstrXeqYplusC::lsFixedCons: Wrong `varFired'" );

		VarX->lsSet(VarY->lsValue()+C, NsList<NsIntVar*>(VarY), this);
	}
}




	void
Ns_ConstrXneqY::lsFixedCons (NsIntVar* varFired)
{
	assert_Ns( varFired->lsIsBound() ,
		"Ns_ConstrXneqY::lsFixedCons: Unbound `varFired'" );

	if ( VarX  ==  varFired )    {

		if ( VarY->lsIsBound()
			&& VarY->lsValue() == varFired->lsValue() )
		{
			VarY->lsSet(NsMINUS_INF, NsList<NsIntVar*>(VarX), this);
		}

	}  else  {

		assert_Ns( VarY == varFired ,
			"Ns_ConstrXneqY::lsFixedCons: Wrong `varFired'" );

		if ( VarX->lsIsBound()
			&& VarX->lsValue() == varFired->lsValue() )
		{
			VarX->lsSet(NsMINUS_INF, NsList<NsIntVar*>(VarY), this);
		}
	}
}




	void
Ns_ConstrAllDiff::lsFixedCons (NsIntVar* varFired)
{
	for (NsIntVarArray::iterator X=VarArr->begin();
			X != VarArr->end();
			++X)
	{
		if ( &*X != varFired  &&  X->lsIsBound()
				&& X->lsValue() == varFired->lsValue() )
		{
			X->lsSet(NsMINUS_INF, NsList<NsIntVar*>(varFired), this);
		}
	}
}




	void
Ns_ConstrXlessthanY::lsFixedCons (NsIntVar* varFired)
{
	assert_Ns( varFired->lsIsBound() ,
		"Ns_ConstrXlessthanY::lsFixedCons: Unbound `varFired'" );

	if ( VarX  ==  varFired )    {

		if ( VarY->lsIsBound()
			&& VarY->lsValue() <= varFired->lsValue() )
		{
			VarY->lsSet(NsMINUS_INF, NsList<NsIntVar*>(VarX), this);
		}

	}  else  {

		assert_Ns( VarY == varFired ,
			"Ns_ConstrXlessthanY::lsFixedCons: Wrong `varFired'" );

		if ( VarX->lsIsBound()
			&& VarX->lsValue() >= varFired->lsValue() )
		{
			VarX->lsSet(NsMINUS_INF, NsList<NsIntVar*>(VarY), this);
		}
	}
}




	void
Ns_ConstrXlesseqthanY::lsFixedCons (NsIntVar* varFired)
{
	assert_Ns( varFired->lsIsBound() ,
		"Ns_ConstrXlesseqthanY::lsFixedCons: Unbound `varFired'" );

	if ( VarX  ==  varFired )    {

		if ( VarY->lsIsBound()
			&& VarY->lsValue() < varFired->lsValue() )
		{
			VarY->lsSet(NsMINUS_INF, NsList<NsIntVar*>(VarX), this);
		}

	}  else  {

		assert_Ns( VarY == varFired ,
			"Ns_ConstrXlesseqthanY::lsFixedCons: Wrong `varFired'" );

		if ( VarX->lsIsBound()
			&& VarX->lsValue() > varFired->lsValue() )
		{
			VarX->lsSet(NsMINUS_INF, NsList<NsIntVar*>(VarY), this);
		}
	}
}




	void
Ns_ConstrXeqYtimesC::lsFixedCons (NsIntVar* varFired)
{
	assert_Ns( varFired->lsIsBound() ,
		"Ns_ConstrXeqYtimesC::lsFixedCons: Unbound `varFired'" );

	if ( VarX  ==  varFired )    {

		if ( VarX->lsValue() % C  ==  0 )
			VarY->lsSet(VarX->lsValue()/C, NsList<NsIntVar*>(VarX), this);
		else
			VarY->lsSet(NsMINUS_INF, NsList<NsIntVar*>(VarX), this);

	}  else  {

		assert_Ns( VarY == varFired ,
			"Ns_ConstrXeqYtimesC::lsFixedCons: Wrong `varFired'" );

		VarX->lsSet(VarY->lsValue()*C, NsList<NsIntVar*>(VarY), this);
	}
}




	void
Ns_ConstrXeqYplusZ::lsFixedCons (NsIntVar* varFired)
{
	assert_Ns( varFired->lsIsBound() ,
		"Ns_ConstrXeqYplusZ::lsFixedCons: Unbound `varFired'" );

	if ( VarX  ==  varFired )    {

		if ( VarY->lsIsBound() )  {

			VarZ->lsSet( (VarX->lsValue() - VarY->lsValue()),
					NsList<NsIntVar*>(VarX,VarY), this);
		}

		if ( VarZ->lsIsBound() )  {

			VarY->lsSet( (VarX->lsValue() - VarZ->lsValue()),
					NsList<NsIntVar*>(VarX,VarZ), this);
		}

	}  else if ( VarY  ==  varFired )    {

		if ( VarX->lsIsBound() )  {

			VarZ->lsSet( (VarX->lsValue() - VarY->lsValue()),
					NsList<NsIntVar*>(VarX,VarY), this);
		}

		if ( VarZ->lsIsBound() )  {

			VarX->lsSet( (VarY->lsValue() + VarZ->lsValue()),
					NsList<NsIntVar*>(VarY,VarZ), this);
		}

	}  else  {

		assert_Ns( VarZ == varFired ,
			"Ns_ConstrXeqYplusZ::lsFixedCons: Wrong `varFired'" );

		if ( VarX->lsIsBound() )  {

			VarY->lsSet( (VarX->lsValue() - VarZ->lsValue()),
					NsList<NsIntVar*>(VarX,VarZ), this);
		}

		if ( VarY->lsIsBound() )  {

			VarX->lsSet( (VarY->lsValue() + VarZ->lsValue()),
					NsList<NsIntVar*>(VarY,VarZ), this);
		}
	}
}
