/*
 * This is the file where the constraints on the model is declared.
 */


% Visit the insert or delete states at most 2 times:

constraint(state_specific(cardinality([insert,delete],2))).
