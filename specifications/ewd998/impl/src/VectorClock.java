import java.util.HashMap;
import java.util.Map;

import com.google.gson.Gson;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.reflect.TypeToken;

public class VectorClock {

	private final Map<Integer, Integer> vc = new HashMap<>();
	// This node's id.
	private final int n;

	public VectorClock(final int n, final int dimension) {
		this.vc.put(n, 0);
		this.n = n;
	}

	public JsonElement tick() {
		// /\ clock' = [ clock EXCEPT ![n][n] = @ + 1 ]
		this.vc.merge(n, 1, Integer::sum);
		return toJson();
	}

	public JsonElement tickAndMerge(final JsonObject json) {
		// Each time a process receives a message, it increments its own logical clock
		// in the vector by one and updates each element in its vector by taking the
		// maximum of the value in its own vector clock and the value in the vector in
		// the received message (for every element).
		// https://en.wikipedia.org/wiki/Vector_clock
		tick();
		
		// De-serialize.
		final TypeToken<Map<Integer, Integer>> typeToken = new TypeToken<Map<Integer, Integer>>() { };
		final Map<Integer, Integer> m = new Gson().fromJson(json, typeToken.getType());
		
		/*
		 * This is where the "magic" of the vector clock happens. 
		 * 
		 * /\ LET Max(a,b) == IF a < b THEN b ELSE a
		 *        Merge(r, l) == [ m \in Node |-> IF m = n THEN l[m] + 1
		 *                                    ELSE Max(r[m], l[m]) ]
		 *    IN clock' = [ clock EXCEPT ![n] = Merge(inbox[n][j].vc, @) ]
		 */
		m.keySet().forEach(key -> this.vc.merge(key, m.get(key), Integer::max));
		
		return toJson();
	}

	public JsonElement toJson() {
		return new Gson().toJsonTree(this.vc);
	}
}
