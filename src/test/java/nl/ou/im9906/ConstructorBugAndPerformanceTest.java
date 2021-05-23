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

    @Test
    public void testPerformanceSemiParallel()
            throws NoSuchFieldException, IllegalAccessException {

        final Map<Integer, String> bigMap = createIdentityHashMapWithoutOverflow();
        final Map<Integer, String> smallMap = createIdentityHashMapWithOverflow();

        final int batchSize = 15;
        long elapsedTimeBigMap = 0L;
        long elapsedTimeSmallMap = 0L;

        // Start the performance comparison
        for (int i = 0; i < (TEST_CAPACITY - batchSize); i += batchSize) {
            elapsedTimeBigMap += putEntries(bigMap, batchSize);
            elapsedTimeSmallMap += putEntries(smallMap, batchSize);
        }

        System.out.println("Elapsed time (millis) for bigMap: " + elapsedTimeBigMap);
        System.out.println("Size of bigMap: " + bigMap.size());
        System.out.println("Elapsed time (millis) for smallMap: " + elapsedTimeSmallMap);
        System.out.println("Size of smallMap: " + smallMap.size());
        System.out.println("Delta (millis): " + (elapsedTimeSmallMap - elapsedTimeBigMap));
        System.out.println("Delta (%): " + (int)(((elapsedTimeSmallMap - elapsedTimeBigMap) / (double) elapsedTimeBigMap) * 100) + "%");
    }

    // This results in a map with capacity 4 (due to an overflow error in the capacity method)
    // The length of the private field 'table' is twice that capacity
    private Map<Integer, String> createIdentityHashMapWithOverflow() throws NoSuchFieldException, IllegalAccessException {
        final Map<Integer, String> map = new IdentityHashMap<>(OVERFLOW_CAPACITY);
        // Check the expected table length
        assertThat(((Object[]) getValueByFieldName(map, "table")).length, is(4 * 2));
        return map;
    }

    // This results in a map with a correctly (as intended) calculated capacity
    // The length of the private field 'table' is twice that capacity
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
