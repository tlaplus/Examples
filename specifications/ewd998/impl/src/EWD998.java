import java.io.DataInputStream;
import java.io.DataOutputStream;
import java.io.InputStream;
import java.io.OutputStream;
import java.net.ConnectException;
import java.net.InetSocketAddress;
import java.net.ServerSocket;
import java.net.Socket;
import java.net.SocketTimeoutException;
import java.util.Map;
import java.util.Random;
import java.util.concurrent.BlockingQueue;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.LinkedBlockingQueue;

import com.google.gson.JsonObject;
import com.google.gson.JsonParser;
import com.google.gson.JsonPrimitive;

public class EWD998 {

	private enum Color {
		black,
		white
	}
	
	private final Random randomWork = new Random();
	private final Map<Integer, Pair> nodes;

	public EWD998(final Map<Integer, Pair> nodes, final int myId, final boolean isInitiator) throws Exception {
		this.nodes = nodes;

		final BlockingQueue<JsonObject> inbox = new LinkedBlockingQueue<>();

		/*
			Init ==
			    /\ active \in [Node -> BOOLEAN]
			    /\ pending = [i \in Node |-> 0]
			    /\ color \in [Node -> Color]
			    /\ counter = [i \in Node |-> 0]
			    /\ token = [pos |-> 0, q |-> 0, color |-> "black"]
			    \* The clock variable is not part of EWD998.
			    /\ clock = [n \in Node |-> [m \in Node |-> 0] ]
		 */
		boolean active = true;
		Color color = Color.white;
		int counter = 0;
		if (isInitiator) {
			// /\ token = [pos |-> 0, q |-> 0, color |-> "black"]
			inbox.put(getTok(0, Color.black));
		}

		boolean terminationDetected = false;

		// --------------------------------------------------------------------------------- //
		
		// Boilerplate: Network receiver thread (after Init because Init adds an element to inbox).
		final ExecutorService executorService = Executors.newSingleThreadExecutor();
		executorService.submit(() -> {
			Thread.currentThread().setName("Receiver #" + myId);
			try (ServerSocket serverSocket = new ServerSocket(nodes.get(myId).port)) {
				while (true) {
					final Socket socket = serverSocket.accept();
					final InputStream inputStream = socket.getInputStream();
					final DataInputStream dataInputStream = new DataInputStream(inputStream);
					final String in = dataInputStream.readUTF();
										
					final JsonObject msg = JsonParser.parseString(in).getAsJsonObject();
					
					inbox.add(msg);
					if (msg.get("type").getAsString().equals("trm")) {
						// See note at marker "aklseflha" below.
						dataInputStream.close();
						inputStream.close();
						socket.close();
						return null;
					}
				}
			} catch (Exception notExpectedToHappen) {
				// Any exception makes the receiver thread die, causing the distributed system
				// to hang because EWD998 does not consider message loss.  A real implementation
				// has to handle exceptions more gracefully.
				notExpectedToHappen.printStackTrace();
				throw notExpectedToHappen;
			} finally {
				// Orderly terminate this executor to not hang indefinitely.
				executorService.shutdown();
			}
		});
		
		// --------------------------------------------------------------------------------- //
		while (true) {
			final JsonObject msg = inbox.take();
			System.out.println(msg);

			int tokenQ = 0;
			Color tokenColor = null;
			
			// --------------------------------------------------------------------------------- //

			// InitiateToken and PassToken
			if (msg.get("type").getAsString().equals("tok")) {
				tokenQ = msg.get("q").getAsInt();
				tokenColor = Color.valueOf(msg.get("color").getAsString());

				if (isInitiator) {
					/*
					InitiateProbe ==
					    /\ token.pos = 0
					    /\ \* previous round inconclusive:
					        \/ token.color = "black"
					        \/ color[0] = "black"
					        \/ counter[0] + token.q > 0
					    /\ ...
					    /\ UNCHANGED <<active, counter, pending>>                
					 */
					terminationDetected = tokenQ + counter == 0 && color == Color.white && tokenColor == Color.white
							&& !active;
				}
			} else if (msg.get("type").getAsString().equals("pl")) {
				/*
					RecvMsg(i) ==
					    /\ pending[i] > 0
					    /\ active' = [active EXCEPT ![i] = TRUE]
					    /\ pending' = [pending EXCEPT ![i] = @ - 1]
					    /\ counter' = [counter EXCEPT ![i] = @ - 1]
					    /\ color' = [ color EXCEPT ![i] = "black" ]
					    /\ UNCHANGED <<token>>
 				 */
				active = true;
				counter--;
				color = Color.black;
			} else if (msg.get("type").getAsString().equals("trm")) {
				// (aklseflha) The termination message "[trm]" is *not* part of EWD998. Here,
				// the initiator sends a trm message to all nodes including itself after
				// detecting termination. A recipient of a trm message closes the receiver's server
				// socket and orderly shuts down its executor service. Additionally, the trm message
				// is added to the inbox to cause this thread (main) to also terminate.
				assert !active;
				assert inbox.isEmpty();
				return;
			} else {
				throw new IllegalArgumentException("Unknown message type");
			}
			
			// --------------------------------------------------------------------------------- //
			
			/*
				SendMsg(i) ==
				    /\ active[i]
				    /\ counter' = [counter EXCEPT ![i] = @ + 1]
				    /\ \E recv \in Node:
				            pending' = [pending EXCEPT ![recv] = @ + 1]
				    /\ UNCHANGED <<active, color, token>>
			 */
			if (active) {
				// Simulate some work...
				Thread.sleep(randomWork.nextInt(100));
				if (randomWork.nextBoolean()) {
					counter++;
					
					// \E rcv \in Node: ... replaced with probabilistic choice.
					sendMsg(myId, randomWork.nextInt(nodes.size()), getPayload());
				}
			}
			
			// --------------------------------------------------------------------------------- //
				
			/*
				Deactivate(i) ==
				    /\ active[i]
				    /\ active' = [active EXCEPT ![i] = FALSE]
				    /\ UNCHANGED <<pending, color, counter, token>>
			 */
			if (active) {
				active = randomWork.nextDouble() < 0.75d;
			}
			
			// --------------------------------------------------------------------------------- //
			
			// InitiateToken and PassToken actions
			// /\ ...
			// /\ token.pos = i
			if (tokenColor != null) {
				if (isInitiator) {
					/*
 				       terminationDetected ==
						  /\ token.pos = 0
						  /\ token.color = "white"
						  /\ token.q + counter[0] = 0
						  /\ color[0] = "white"
						  /\ ~ active[0]

					 */
					/*
						InitiateProbe ==
						    /\ ...
						    /\ token' = [ pos |-> N-1, q |-> 0, color |-> "white"]
						    /\ color' = [ color EXCEPT ![0] = "white" ]
						    /\ UNCHANGED <<active, counter, pending>>                
					 */
					if (!terminationDetected) {
						sendMsg(myId, nodes.size() - 1, getTok(0, Color.white));
						color = Color.white;
					} else {
						for (Integer n : nodes.keySet()) {
							sendMsg(myId, n, getTrm());
						}
					}
					tokenColor = null;
				} else if (!active) {
					/*
						PassToken(i) ==
						    /\ ~ active[i]
						    /\ token.pos = i
						    /\ token' = [ token EXCEPT !.pos = @ - 1,
						                               !.q   = @ + counter[i],
						                               !.color = IF color[i] = "black" THEN "black" ELSE @ ]
						    /\ color' = [ color EXCEPT ![i] = "white" ]
						    /\ UNCHANGED <<active, pending, counter>>
 					 */
					sendMsg(myId, myId - 1, getTok(tokenQ + counter, color == Color.black ? Color.black : tokenColor));
					color = Color.white;

					tokenColor = null;
				} else {
					// This node owns the token and is active; keep the unchanged token.
					/*
						Deactivate(i) ==
							    /\ ...
							    /\ UNCHANGED <<..., token>>
						SendMsg(i) ==
						    /\ ...
						    /\ UNCHANGED <<..., token>>
						RecvMsg(i) ==
						    /\ ...
						    /\ UNCHANGED <<token>>
				     */
					inbox.add(msg);
				}
			}
		}
	}

	private JsonObject getPayload() throws Exception {
		final JsonObject result = new JsonObject();
		result.add("type", new JsonPrimitive("pl"));
		return result;
	}

	private JsonObject getTok(final int q, final Color color) throws Exception {
		final JsonObject result = new JsonObject();
		result.add("type", new JsonPrimitive("tok"));
		result.add("q", new JsonPrimitive(q));
		result.add("color", new JsonPrimitive(color.toString()));
		return result;
	}

	private JsonObject getTrm() throws Exception {
		final JsonObject result = new JsonObject();
		result.add("type", new JsonPrimitive("trm"));
		return result;
	}

	// Boilerplate: Sending messages. 
	private void sendMsg(final int sender, final int receiver, final JsonObject msg) throws Exception {
		System.out.println(msg);
		
		final Pair p = nodes.get(receiver);
		int retry = 1;
		while (true) {
			try (Socket socket = new Socket()) {
				// Increase the connection's timeout if the receiver hasn't started listening yet.
				socket.connect(new InetSocketAddress(p.host, p.port), 1000 * retry++);
				final OutputStream outputStream = socket.getOutputStream();
				final DataOutputStream dataOutputStream = new DataOutputStream(outputStream);
						
				dataOutputStream.writeUTF(msg.toString());
				dataOutputStream.flush();
				dataOutputStream.close();
				
				socket.close();
				return;
			} catch (SocketTimeoutException | ConnectException thisIsFineWillRetry) {
				if (retry > 3) {
					// Stay silent if it failed less than three times. If it fails more than three
					// times, the user will likely want to inspect.  Note that EWD998 assumes
					// reliable message infrastructure and doesn't consider network failure.
					thisIsFineWillRetry.printStackTrace();
				}
				Thread.sleep(500L * retry);
			}
		}
	}
}
