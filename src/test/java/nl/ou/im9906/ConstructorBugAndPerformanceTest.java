package nl.ou.im9906;

import org.junit.Test;

import java.util.Date;
import java.util.IdentityHashMap;
import java.util.Map;

import static nl.ou.im9906.ReflectionUtils.getValueByFieldName;
import static org.hamcrest.MatcherAssert.assertThat;
import static org.hamcrest.core.Is.is;

public class ConstructorBugAndPerformanceTest {

    private final static int TEST_CAPACITY = 1 << 23;
    private final static int OVERFLOW_CAPACITY = 1431655765;

    /**
     * Fills two maps with entries. One map has an initially large table (so there is no need to resize during or after
     * a put), the other has an initially small table (and will therefore be resized when there is insufficient room
     * for new entries).
     * <p/>
     * The exercise is repeated several times with different batch sizes.
     *
     * @throws NoSuchFieldException
     * @throws IllegalAccessException
     */
    @Test
    public void testPerformanceSemiParallel()
            throws NoSuchFieldException, IllegalAccessException {

        long elapsedTimeMapWithInitiallyLargeTable = 0L;
        long elapsedTimeMapWithInitiallySmallTable = 0L;
        for (int batchSize = 1; batchSize < TEST_CAPACITY; batchSize *= 2) {
            long[] elapsedTimes = putEntriesInBatchOfSize(batchSize);

            System.out.println("Batch size: " + batchSize);
            System.out.println("Elapsed time (millis) for map with initially large table: " + elapsedTimes[0]);
            System.out.println("Elapsed time (millis) for map with initially small table: " + elapsedTimes[1]);
            System.out.println("Delta (millis): " + (elapsedTimes[1] - elapsedTimes[0]));
            System.out.println("");

            elapsedTimeMapWithInitiallyLargeTable += elapsedTimes[0];
            elapsedTimeMapWithInitiallySmallTable += elapsedTimes[1];
        }

        System.out.println("Total elapsed time (millis) for map with initially large table: " + elapsedTimeMapWithInitiallyLargeTable);
        System.out.println("Total elapsed time (millis) for map with initially small table: " + elapsedTimeMapWithInitiallySmallTable);
        final long delta = elapsedTimeMapWithInitiallySmallTable - elapsedTimeMapWithInitiallyLargeTable;
        System.out.println("Delta (millis): " + delta);
        System.out.println("Delta (%): " + (int) ((delta / (double) elapsedTimeMapWithInitiallyLargeTable) * 100) + "%");
    }

    /**
     * This method puts batches of entries into two maps. The total number of entries added is the number of batches
     * that fit into {@link #TEST_CAPACITY}. First, a batch is put into one map, then a batch is put into the ohter
     * map, and this is repeated until the next batch would supersede the value of {@link #TEST_CAPACITY}.
     *
     * @param batchSize the size of one batch.
     * @return the elapsed time while putting the entries for each map (elapsedTimes[0] refers to the time elapsed
     * while putting entries in bigMap, and elapsedTime[1] refers to the time elapsed while putting entries in
     * smallMap)
     * @throws NoSuchFieldException
     * @throws IllegalAccessException
     */
    private long[] putEntriesInBatchOfSize(final int batchSize) throws NoSuchFieldException, IllegalAccessException {
        final Map<Integer, String> bigMap = createIdentityHashMapWithoutOverflow();
        final Map<Integer, String> smallMap = createIdentityHashMapWithOverflow();

        // Start the performance comparison
        long[] elapsedTimes = {0L, 0L};
        for (int i = 0; i < (TEST_CAPACITY - batchSize); i += batchSize) {
            elapsedTimes[0] += putEntries(bigMap, batchSize);
            elapsedTimes[1] += putEntries(smallMap, batchSize);
        }
        return elapsedTimes;
    }

    /**
     * This method creates a map with a capacity of four entries, due to an overflow error in the capacity method.
     * The length of the private field 'table' is twice that capacity.
     *
     * @return the created map.
     * @throws NoSuchFieldException
     * @throws IllegalAccessException
     */
    private Map<Integer, String> createIdentityHashMapWithOverflow() throws NoSuchFieldException, IllegalAccessException {
        final Map<Integer, String> map = new IdentityHashMap<>(OVERFLOW_CAPACITY);
        // Check the expected table length
        assertThat(((Object[]) getValueByFieldName(map, "table")).length, is(4 * 2));
        return map;
    }

    /**
     * This method creates a map with a correctly (as intended) calculated capacity, without an overflow error.
     * The length of the private field 'table' is twice that capacity.
     *
     * @return the created map.
     * @throws NoSuchFieldException
     * @throws IllegalAccessException
     */
    private Map<Integer, String> createIdentityHashMapWithoutOverflow() throws NoSuchFieldException, IllegalAccessException {
        final Map<Integer, String> map = new IdentityHashMap<>(TEST_CAPACITY);
        int expectedSize = 4;
        while (expectedSize < (3 * TEST_CAPACITY) / 2) {
            expectedSize <<= 1;
        }
        int expectedTableLen = expectedSize * 2;
        // Check the expected table length
        assertThat(((Object[]) getValueByFieldName(map, "table")).length, is(expectedTableLen));
        return map;
    }

    /**
     * Puts a number of entries into a map. The keys of the entries equal there index number, and the values are
     * a String containing "aValue". It returns the time needed to do so in millis.
     *
     * @param map                  the map to put the entries into
     * @param numberOfEntriesToAdd the number of entries added to the map
     * @return the elapsed milliseconds to fulfill the task
     */
    private long putEntries(Map<Integer, String> map, int numberOfEntriesToAdd) {
        final long startTime = new Date().getTime();
        final int startIndex = map.size();
        for (int i = startIndex; i < startIndex + numberOfEntriesToAdd; i++) {
            final Integer key = new Integer(i);
            map.put(key, "aValue");
        }
        final long endTime = new Date().getTime();
        return endTime - startTime;
    }
}
