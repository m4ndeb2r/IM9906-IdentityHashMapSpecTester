package nl.ou.im9906;

import org.junit.Before;
import org.junit.Ignore;
import org.junit.Test;

import java.util.ArrayList;
import java.util.Collection;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map.Entry;
import java.util.Set;

import static nl.ou.im9906.ClassInvariantTestHelper.assertClassInvariants;
import static nl.ou.im9906.ReflectionUtils.setValueByFieldName;
import static org.hamcrest.MatcherAssert.assertThat;
import static org.hamcrest.core.Is.is;
import static org.junit.Assert.fail;

/**
 * This test class tests some of the JML specs added to the {@link IdentityHashMap}
 * in the 'IM9906 VerifiyingIdentityHashMap' project that aims to formally specify
 * that class.
 * <p>
 * For example, in this test class we play around with the {@link IdentityHashMap}
 * of the JDK7 (the version of the class under analysis), and with each step we check
 * if the class invariant(s) of the class and its inner classes still hold. This way
 * we can perform some preliminary sanity checks on these invariants to see if they
 * themselves are okay. (If one of the tests fails, there is, in theory, a chance that
 * the {@link IdentityHashMap} contains a bug, but it is more likely that the JML
 * specs (or the representation in this test class) contain an error.)
 */
public class IdentityHashMapClassInvariantTest {

    // The test subject
    private IdentityHashMap<Object, Object> map;

    @Before
    public void setUp() {
        map = new IdentityHashMap<>();
    }

    /**
     * Tests of the class invariants hold after invocation of the several constructors
     * of the {@link IdentityHashMap}.
     *
     * @throws NoSuchFieldException   if any of the expected private fields does not exist
     * @throws IllegalAccessException if it was not possible to get access to a required private field
     * @throws NoSuchClassException   if any of the expected inner classes does not exist
     */
    @Test
    public void testClassInvariantsAfterConstructorInvocation()
            throws NoSuchFieldException, IllegalAccessException, NoSuchClassException {
        assertClassInvariants(map);

        map = new IdentityHashMap<>(1 << 20);
        assertClassInvariants(map);
        map.values();
        map.keySet();
        map.entrySet();
        assertClassInvariants(map);

        map = new IdentityHashMap<>(0);
        assertClassInvariants(map);
        map.values();
        map.keySet();
        map.entrySet();
        assertClassInvariants(map);

        map = new IdentityHashMap<>(map);
        assertClassInvariants(map);
        try {
            map = new IdentityHashMap<>((IdentityHashMap<?, ?>) null);
            fail("Expected NullPointerException");
        } catch (NullPointerException e) {
            // Ok. Expected.
        }
    }

    /**
     * Tests is the class invariants hold after adding and removing elements
     * to the {@link IdentityHashMap}, and cloning an cleaning it.
     *
     * @throws NoSuchFieldException   if any of the expected private fields does not exist
     * @throws IllegalAccessException if it was not possible to get access to a required private field
     * @throws NoSuchClassException   if any of the expected inner classes does not exist
     */
    @Test
    public void testClassInvariantsAfterPutRemoveClearClone()
            throws NoSuchFieldException, IllegalAccessException, NoSuchClassException {
        assertClassInvariants(map);

        final List<String> keys = new ArrayList<>();
        for (int i = 0; i < 2000; i++) {
            keys.add("key" + i);
        }

        // Add some entries
        for (String key : keys) map.put(key, "someValue");
        Set<Object> keySet = map.keySet();
        Collection<Object> values = map.values();
        Set<Entry<Object, Object>> entries = map.entrySet();
        assertThat(map.size(), is(keys.size()));
        assertThat(entries.size(), is(map.size()));
        assertThat(keySet.size(), is(map.size()));
        assertThat(values.size(), is(map.size()));
        assertClassInvariants(map);

        // Overwrite values of existing entries
        for (String key : keys) map.put(key, "someOtherValue");
        keySet = map.keySet();
        values = map.values();
        entries = map.entrySet();
        assertThat(map.size(), is(keys.size()));
        assertThat(entries.size(), is(map.size()));
        assertThat(keySet.size(), is(map.size()));
        assertThat(values.size(), is(map.size()));
        assertClassInvariants(map);

        // Clone the map
        final IdentityHashMap<Object, Object> clone = (IdentityHashMap<Object, Object>) map.clone();

        // Remove all elements from the original map
        for (String key : keys) map.remove(key);
        assertThat(map.size(), is(0));
        assertThat(entries.size(), is(map.size()));
        assertThat(keySet.size(), is(map.size()));
        assertThat(values.size(), is(map.size()));
        assertClassInvariants(map);

        // Check is the clone is still untouched
        keySet = clone.keySet();
        values = clone.values();
        entries = clone.entrySet();
        assertThat(clone.size(), is(keys.size()));
        assertThat(entries.size(), is(clone.size()));
        assertThat(keySet.size(), is(clone.size()));
        assertThat(values.size(), is(clone.size()));
        assertClassInvariants(clone);

        // Clean the clone
        clone.clear();
        assertThat(clone.size(), is(0));
        assertThat(entries.size(), is(0));
        assertThat(keySet.size(), is(0));
        assertThat(values.size(), is(0));
        assertClassInvariants(clone);
    }

    /**
     * A test with nested {@link IdentityHashMap}s, to see if the class invariants
     * still hold after several operations on the maps.
     *
     * @throws NoSuchFieldException   if any of the expected private fields does not exist
     * @throws IllegalAccessException if it was not possible to get access to a required private field
     * @throws NoSuchClassException   if any of the expected inner classes does not exist
     */
    @Test
    @Ignore // Temporarily ignore, because this test takes up a lot of time
    public void testClassInvariantsForRecursiveIdentityHashMap()
            throws NoSuchFieldException, IllegalAccessException, NoSuchClassException {
        assertClassInvariants(map);

        final Set<Entry<Object, Object>> entries = map.entrySet();
        final Set<Object> keySet = map.keySet();
        final Collection<Object> values = map.values();
        assertClassInvariants(map);

        for (int i = 0; i < 2000; i++) {
            map.put(map.clone(), entries);
            assertClassInvariants(map);
        }
        assertThat(map.size(), is(2000));
        assertThat(entries.size(), is(map.size()));
        assertThat(keySet.size(), is(map.size()));
        assertThat(values.size(), is(map.size()));
        map.putAll(map);
        assertThat(map.size(), is(2000));
        assertThat(entries.size(), is(map.size()));
        assertThat(keySet.size(), is(map.size()));
        assertThat(values.size(), is(map.size()));
        assertClassInvariants(map);

        while (map.size() > 1000) {
            map.remove(map.keySet().toArray()[map.size() - 1]);
            assertClassInvariants(map);
        }
        assertThat(map.size(), is(1000));
        assertThat(entries.size(), is(map.size()));
        assertThat(keySet.size(), is(map.size()));
        assertThat(values.size(), is(map.size()));
        assertClassInvariants(map);

        map.clear();
        assertThat(map.size(), is(0));
        assertThat(entries.size(), is(map.size()));
        assertThat(keySet.size(), is(map.size()));
        assertThat(values.size(), is(map.size()));
        assertClassInvariants(map);
    }

    /**
     * Tests if the class invariants still hold after the modCount field overflows
     * (which will happen after too many modifications of the {@link IdentityHashMap},
     * but should not cause any real errors). The modCount field is set to a large
     * number (Integer.MAX_VALUE - 1) using reflection. After that, some testing is
     * done by modifying the map.
     *
     * @throws NoSuchFieldException   if any of the expected private fields does not exist
     * @throws IllegalAccessException if it was not possible to get access to a required private field
     * @throws NoSuchClassException   if any of the expected inner classes does not exist
     */
    @Test
    public void testClassInvariantsWithLargeModCountInIdentityHashMap()
            throws NoSuchFieldException, IllegalAccessException, NoSuchClassException {
        setValueByFieldName((IdentityHashMap<?, ?>) map, "modCount", Integer.MAX_VALUE - 1);
        for (int i = 0; i < 3; i++) {
            map.put("key" + i, "val" + i);
            assertClassInvariants(map);
        }
        map.clear();
        assertClassInvariants(map);
    }

    @Test
    public void testUniquenessOfKeys()
            throws IllegalAccessException, NoSuchClassException, NoSuchFieldException {
        String key = "key";
        map.put(key, "val1");
        map.put(key, "val2");
        assertThat(map.size(), is(1));
        assertClassInvariants(map);
    }
}
