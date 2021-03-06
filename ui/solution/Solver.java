/*
 *
 * Project TouIST, 2015. Easily formalize and solve real-world sized problems
 * using propositional logic and linear theory of reals with a nice GUI.
 *
 * https://github.com/olzd/touist
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the GNU Lesser General Public License
 * (LGPL) version 2.1 which accompanies this distribution, and is available at
 * http://www.gnu.org/licenses/lgpl-2.1.html
 *
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU
 * Lesser General Public License for more details.
 *
 * Contributors:
 *     Alexis Comte, Abdelwahab Heba, Olivier Lezaud,
 *     Skander Ben Slimane, Maël Valais
 *
 */

package solution;

import java.io.IOException;

import entity.Model;

/**
 * A sub-class must implement Solver. The inherited class allows the user to
 * launch the solver program with the right DIMACS input, let him know if the
 * given problem is satisfiable and then give the user an iterable "Models". The
 * user can also close the solver if needed. (that is running background).
 *
 * @author Abdel
 * @modified Maël
 */
public abstract class Solver {

	public Solver() {
		super();
	}

	/**
	 * Launch the solver program in background. Does not check satisfiability
	 * but waits for the ModelsIterator.hasNext() to retrieve the next model.
	 * @param dimacsFilesPath The DIMACS file path
	 * @return the iterable Models instance.
	 * @throws IOException
	 */
	public abstract void launch() throws IOException;

	/**
	 * Asks the solver if any models exist. The user MUST check
	 * that before getting the model list.
	 * @return the satisfiability
	 */
	public abstract boolean isSatisfiable();
	/**
	 * Close the solver program process.
	 */
	public abstract void close();

	/**
	 * WARNING: you must run isSatisfiable() BEFORE using this method.
	 * Gives the list of models on which the user can iterate. The only way to
	 * get the "next" models is to iterate. The size of Models is not known
	 * unless hasNext() returns false.
	 * Use this method after using launch().
	 * @return the models
	 * @throws NotSatisfiableException if not satisfiable
	 * @throws SolverExecutionException if any error happened
	 */
	public abstract ModelList getModelList() throws NotSatisfiableException,SolverExecutionException;

	/**
	 * ONLY used by ModelsIterator.
	 * @return the model if there was a model, null if there is no model left.
	 * @throws IOException
	 * @throws NotSatisfiableException
	 * @throws SolverExecutionException
	 */
	protected abstract Model nextModel() throws IOException, NotSatisfiableException, SolverExecutionException;

	/**
	 * ONLY used by ModelsIterator
	 * @param rawModelOutput The output
	 * @return a model with, if a literalMap was given, the translated literal.
	 * If no literalMap is given, the Model stores the literal as given by the
	 * solver (an integer).
	 * @throws NotSatisfiableException if not satisfiable
	 */
	protected abstract Model parseModel(String[] rawModelOutput) throws NotSatisfiableException;
}
