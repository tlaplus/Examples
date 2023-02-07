import java.util.HashMap;
import java.util.Map;
import java.util.Random;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.TimeUnit;

public class EWD998App {
    private static final int N = 9;
	
	private static final String HOSTNAME = "localhost";
	private static final int BASEPORT = 4223;
	
	public static void main(String[] args) throws Exception {
		final Random rnd = new Random();
		
		int traces = 0;
		while (true) {
			// Test with n \in 1..N nodes.
			final int n = args.length > 1 ? Integer.parseInt(args[1]) : rnd.nextInt(N) + 1;
			
			// Reversed order starting the initiator node last; initiator would fail when
			// the receiver isn't up when the initiator sends out the first message.  The
			// initiator is the last to join and the last to leave the party.
			final ExecutorService executor = Executors.newFixedThreadPool(n);
			for (int i = n - 1; i >= 0; i--) {

				final Map<Integer, Pair> nodes = new HashMap<>(n);
				for (int j = 0; j < n; j++) {
					nodes.put(j, new Pair(HOSTNAME, BASEPORT + j));
				}
				final int myId = i;
				
				// Cannot .get() the task because the runners would run sequentially and each
				// run blocks until termination is detected.
				executor.submit(() -> {
					Thread.currentThread().setName("Node #" + myId);
					try {
						new EWD998(nodes, myId, myId == 0);	
					} catch (Exception e) {
						e.printStackTrace();
					}
					return null;
				});
			}
			
			// Wait forever for the executor to terminate.
			executor.shutdown();
			executor.awaitTermination(Long.MAX_VALUE, TimeUnit.DAYS);
			
			if (args.length > 0) {
				// Terminate after M traces if an integer value
				// M is passed as the first argument to this main.
				if (++traces >= Integer.parseInt(args[0])) {
					return;
				}
			}

			// Allow the OS to fully close sockets and reclaim fds.
			Thread.sleep(5000);
		}
	}
}
