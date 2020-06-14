package nl.ou.im9906;

import org.junit.Before;
import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.ExpectedException;

import java.lang.reflect.Field;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.util.AbstractMap;
import java.util.Collection;
import java.util.IdentityHashMap;
import java.util.Iterator;
import java.util.Map.Entry;
import java.util.Set;

import static org.hamcrest.MatcherAssert.assertThat;
import static org.hamcrest.core.Is.is;

/**
 * This test class tests some of the JML specs added to the {@link IdentityHashMap}
 * in the 'IM9906 VerifiyingIdentityHashMap' project that aims to formally specify
 * that class.
 * <p>
 * For example, in this test class we play call the methods in the {@link IdentityHashMap}
 * of the JDK7 (the version of the class under analysis), and try to test the JML specs
 * of these methods. This way we can perform some preliminary sanity checks on these specs
 * to see if they themselves are okay. (If one of the tests fails, there is, in theory, a
 * chance that the {@link IdentityHashMap} contains a bug, but it is more likely that the
 * JML specs (or the representation in this test class) contain an error.)
 */
public class IdentityHashMapMethodSpecsTest {

    // Set this constant to true for extra output
    private static final boolean VERBOSE = true;

    // The test subject
    private IdentityHashMap<Object, Object> map;

    @Rule
    public ExpectedException expectedException = ExpectedException.none();

    @Before
    public void setUp() {
        map = new IdentityHashMap<>();
    }

    /**
     * Tests the postcondition of the default constructor of the {@link IdentityHashMap}. The
     * length of the private field table is expected to be 2 * DEFAULT_CAPACITY = 64, and the
     * exptected size of the map is 0.
     *
     * @throws NoSuchFieldException   if the expected private field table does not exist
     * @throws IllegalAccessException if it was not possible to get acces to the private field
     */
    @Test
    public void testDefaultConstructorPostCondition()
            throws NoSuchFieldException, IllegalAccessException {
        final int defaultCapacity = getIntegerFieldByName(map, "DEFAULT_CAPACITY");
        assertThat(getTable(map).length, is(2 * defaultCapacity));
        assertThat(map.size(), is(0));
    }

    /**
     * Tests the postcondition of the constructor of the {@link IdentityHashMap} accepting a
     * preferred capacity for an argument. When a negative value is passed, an
     * IllegalArgumentException is expected.
     */
    @Test
    public void testConstructorWithPreferredCapacityExceptionalBehavior() {
        expectedException.expect(IllegalArgumentException.class);
        new IdentityHashMap<>(-1);
    }

    /**
     * Tests the postcondition of the constructor of the {@link IdentityHashMap} accepting a
     * expected max size for an argument. When a non-negative value is passed, we expect the
     * length of the table array to be determined by the capacity method.
     *
     * @throws NoSuchMethodException
     * @throws InvocationTargetException
     * @throws IllegalAccessException
     * @throws NoSuchFieldException
     */
    @Test
    public void testConstructorWithExpectedMaxSizeNormalBehavior()
            throws NoSuchMethodException, InvocationTargetException, IllegalAccessException, NoSuchFieldException {
        IdentityHashMap<String, String> map = new IdentityHashMap<>(0);
        int capacity = invokeCapacity(0, map);
        assertThat(getTable(map).length, is(2 * capacity));
        assertThat(map.size(), is(0));

        final int largeInt = Integer.MAX_VALUE / 1024;
        map = new IdentityHashMap<>(largeInt);
        capacity = invokeCapacity(largeInt, map);
        assertThat(getTable(map).length, is(2 * capacity));
        assertThat(map.size(), is(0));
    }

    // Invokes the private method 'capacity' of the specified map, with the specified
    // expectedMaxSize.
    private int invokeCapacity(int expectedMaxSize, IdentityHashMap<?, ?> map)
            throws NoSuchMethodException, IllegalAccessException, InvocationTargetException {
        final Method[] declaredMethods = IdentityHashMap.class.getDeclaredMethods();
        for (Method method : declaredMethods) {
            if (method.getName().equals("capacity")) {
                method.setAccessible(true);
                return (int) method.invoke(map, expectedMaxSize);
            }
        }
        throw new NoSuchMethodException("Method 'capacity' not found in class 'IdentityHashMap'.");
    }

    /**
     * Get the value of the private field table from the specified map using
     * reflection.
     *
     * @param map an instance of the {@link IdentityHashMap}
     * @return the private table field
     * @throws NoSuchFieldException
     * @throws IllegalAccessException
     */
    private Object[] getTable(IdentityHashMap<?, ?> map)
            throws NoSuchFieldException, IllegalAccessException {
        final Field tableField = IdentityHashMap.class.getDeclaredField("table");
        tableField.setAccessible(true);
        return (Object[]) tableField.get(map);
    }

    /**
     * Get the value of integer field with the specified fieldName from the specified
     * map using reflection.
     *
     * @param map       an instance of the {@link IdentityHashMap}
     * @param fieldName the name of the private field to get (this must be a field of
     *                  type integer)
     * @return the value of requested field
     * @throws NoSuchFieldException
     * @throws IllegalAccessException
     */
    private int getIntegerFieldByName(IdentityHashMap<?, ?> map, String fieldName)
            throws NoSuchFieldException, IllegalAccessException {
        final Field field = IdentityHashMap.class.getDeclaredField(fieldName);
        field.setAccessible(true);
        return (Integer) field.get(map);
    }

    /**
     * Set the value of the integer field with the specified fieldName in the specified
     * map using reflection.
     *
     * @param map       an instance of the {@link IdentityHashMap}
     * @param fieldName the name of the field that is to be modified
     * @param value     the new value of the field
     * @throws NoSuchFieldException
     * @throws IllegalAccessException
     */
    private void setIntegerFieldByName(IdentityHashMap<?, ?> map, String fieldName, int value)
            throws NoSuchFieldException, IllegalAccessException {
        final Field field = IdentityHashMap.class.getDeclaredField(fieldName);
        field.setAccessible(true);
        field.set(map, value);
    }

    /**
     * Get the value of the field entrySet from the specified map using reflection.
     *
     * @param map an instance of the {@link IdentityHashMap}
     * @return the private entrySet field
     * @throws NoSuchFieldException
     * @throws IllegalAccessException
     */
    private Set<Entry<?, ?>> getEntrySet(IdentityHashMap<?, ?> map)
            throws NoSuchFieldException, IllegalAccessException {
        final Field entrySetField = IdentityHashMap.class.getDeclaredField("entrySet");
        entrySetField.setAccessible(true);
        return (Set<Entry<?, ?>>) entrySetField.get(map);
    }

    /**
     * Get the private integer field with the specified fieldName from the
     * IdentityHashMap$EntryIterator inner class, using reflection.
     *
     * @param entryIterator an instance of the IdentityHashMap$EntryIterator
     * @param fieldName     the name of the requested field
     * @return the value of the requested field
     * @throws NoSuchFieldException   if the request field does not exist
     * @throws IllegalAccessException if it was not possible to get access to the field
     * @throws NoSuchClassException   if the inner class EntryIterator does not exist
     */
    private Integer getIntegerFieldByNameFromEntryIterator(Iterator<Entry<?, ?>> entryIterator, String fieldName)
            throws NoSuchFieldException, IllegalAccessException, NoSuchClassException {
        final Class<?> entryIteratorClass = getInnerClass("EntryIterator");
        Field declaredField;
        try {
            declaredField = entryIteratorClass.getDeclaredField(fieldName);
        } catch (NoSuchFieldException e) {
            final Class<?> identityHashMapIteratorClass = entryIteratorClass.getSuperclass();
            declaredField = identityHashMapIteratorClass.getDeclaredField(fieldName);
        }
        declaredField.setAccessible(true);
        return (Integer) declaredField.get(entryIterator);
    }

    /**
     * Get the traversalTable field from the IdentityHashMap$EntryIterator inner class,
     * using reflection.
     *
     * @param entryIterator an instance of the IdentityHashMap$EntryIterator
     * @return the requested traversalTable field, or {@code null} if it is not instantiated
     * @throws NoSuchFieldException   if the field traversalTable does not exist
     * @throws IllegalAccessException if it was not possible to get access to the field
     * @throws NoSuchClassException   if the inner class EntryIterator does not exist
     */
    private Object[] getTraversalTableFromEntryIterator(Iterator<Entry<?, ?>> entryIterator)
            throws NoSuchFieldException, IllegalAccessException, NoSuchClassException {
        final Class<?> entryIteratorClass = getInnerClass("EntryIterator");
        final Class<?> identityHashMapIteratorClass = entryIteratorClass.getSuperclass();
        final Field traversalTableField = identityHashMapIteratorClass.getDeclaredField("traversalTable");
        traversalTableField.setAccessible(true);
        return (Object[]) traversalTableField.get(entryIterator);
    }

    /**
     * Get the private lastReturnedEntry from the IdentityHashMap$EntryIterator inner class,
     * using reflection.
     *
     * @param entryIterator an instance of the IdentityHashMap$EntryIterator
     * @return the requested lastReturnedEntry field, or {@code null} if it is not instantiated
     * @throws NoSuchFieldException   if the field lastReturnedEntry does not exist
     * @throws IllegalAccessException if it was not possible to get access to the field
     * @throws NoSuchClassException   if the inner class EntryIterator does not exist
     */
    private Entry<?, ?> getLastReturnedEntryFromEntryIterator(Iterator<Entry<?, ?>> entryIterator)
            throws NoSuchFieldException, NoSuchClassException, IllegalAccessException {
        final Class<?> entryIteratorClass = getInnerClass("EntryIterator");
        final Field lastReturnedEntryField = entryIteratorClass.getDeclaredField("lastReturnedEntry");
        lastReturnedEntryField.setAccessible(true);
        return (Entry<?, ?>) lastReturnedEntryField.get(entryIterator);
    }

    /**
     * Get the private integer field with the specified fieldName from the
     * IdentityHashMap$EntryIterator$Entry inner class, using reflection.
     *
     * @param entry     an instance of the IdentityHashMap$EntryIterator$Entry class
     * @param fieldName the name of the requested integer field
     * @return the value of the requested field
     * @throws NoSuchFieldException   if the field does not exist
     * @throws IllegalAccessException if it was not possible to get access to the field
     * @throws NoSuchClassException   if one of the expected inner classes does not exist
     */
    private Integer getIntegerFieldByNameFromEntry(Entry<?, ?> entry, String fieldName)
            throws NoSuchFieldException, IllegalAccessException, NoSuchClassException {
        final Class<?> entryIteratorClass = getInnerClass("EntryIterator");
        final Class<?> entryClass = getInnerClass(entryIteratorClass, "Entry");
        final Field declaredField = entryClass.getDeclaredField(fieldName);
        declaredField.setAccessible(true);
        return (Integer) declaredField.get(entry);
    }

    /**
     * Get the value of the private field values from the specified map's parent class
     * ({@link AbstractMap}) using reflection.
     *
     * @param map an instance of the {@link IdentityHashMap}
     * @return the content of the private field values
     * @throws NoSuchFieldException   if the field values does not exist
     * @throws IllegalAccessException if it was not possible to get access to the field
     */
    private Collection<?> getValues(IdentityHashMap<?, ?> map)
            throws NoSuchFieldException, IllegalAccessException {
        final Field valuesField = AbstractMap.class.getDeclaredField("values");
        valuesField.setAccessible(true);
        return (Collection<Object>) valuesField.get(map);
    }

    /**
     * Get the private integer field with the specified fieldName from the
     * IdentityHashMap$ValueIterator inner class, using reflection.
     *
     * @param valueIterator an instance of the IdentityHashMap$ValueIterator
     * @param fieldName     the name of the field to get the value from
     * @return the value of the requested field, or {@code null} if it is not instantiated
     * @throws NoSuchFieldException   if the requested field does not exist
     * @throws IllegalAccessException if it was not possible to ge access to the field
     * @throws NoSuchClassException   if the inner class ValueIterator does not exist
     */
    private Integer getIntegerFieldByNameFromValueIterator(Iterator<?> valueIterator, String fieldName)
            throws NoSuchFieldException, IllegalAccessException, NoSuchClassException {
        final Class<?> valueIteratorClass = getInnerClass("ValueIterator");
        Field declaredField;
        try {
            declaredField = valueIteratorClass.getDeclaredField(fieldName);
        } catch (NoSuchFieldException e) {
            final Class<?> identityHashMapIteratorClass = valueIteratorClass.getSuperclass();
            declaredField = identityHashMapIteratorClass.getDeclaredField(fieldName);
        }
        declaredField.setAccessible(true);
        return (Integer) declaredField.get(valueIterator);
    }

    /**
     * Get the traversalTable field from the IdentityHashMap$ValueIterator inner class,
     * using reflection.
     *
     * @param valueIterator an instance of the IdentityHashMap$ValueIterator
     * @return the requested traversalTable field, or {@code null} if it is not instantiated
     * @throws NoSuchFieldException   if the field traversalTable does not exist
     * @throws IllegalAccessException if it was not possible to get access to the field
     * @throws NoSuchClassException   if the inner class ValueIterator does not exist
     */
    private Object[] getTraversalTableFromValueIterator(Iterator<?> valueIterator)
            throws NoSuchFieldException, IllegalAccessException, NoSuchClassException {
        final Class<?> valueIteratorClass = getInnerClass("ValueIterator");
        final Class<?> identityHashMapIteratorClass = valueIteratorClass.getSuperclass();
        final Field traversalTableField = identityHashMapIteratorClass.getDeclaredField("traversalTable");
        traversalTableField.setAccessible(true);
        return (Object[]) traversalTableField.get(valueIterator);
    }

    /**
     * Get the content of the field keySet from the specified map's parent ({@link AbstractMap})
     * using reflection.
     *
     * @param map an instance of the {@link IdentityHashMap}
     * @return the requested set, or {@code null} if it is not instantiated
     * @throws NoSuchFieldException   if the field keySet does not exist
     * @throws IllegalAccessException if it was not possible to get access to the field
     */
    private Set<?> getKeySet(IdentityHashMap<?, ?> map)
            throws NoSuchFieldException, IllegalAccessException {
        final Field keySetField = AbstractMap.class.getDeclaredField("keySet");
        keySetField.setAccessible(true);
        return (Set<Object>) keySetField.get(map);
    }

    /**
     * Get the private integer value of the field with the specified fieldName from the
     * IdentityHashMap$KeyIterator inner class, using reflection.
     *
     * @param keyIterator an instance of the IdentityHashMap$KeyIterator
     * @param fieldName   the name of the requested field (which must be of type integer)
     * @return the value of the requested field, or {@code null} if it is not instantiated
     * @throws NoSuchFieldException   if the requested field does not exist
     * @throws IllegalAccessException if it was not possible to get access toe the field
     * @throws NoSuchClassException   if the inner class KeyIterator does not exist
     */
    private Integer getIntegerFieldByNameFromKeyIterator(Iterator<?> keyIterator, String fieldName)
            throws NoSuchFieldException, IllegalAccessException, NoSuchClassException {
        final Class<?> keyIteratorClass = getInnerClass("KeyIterator");
        final Class<?> identityHashMapIteratorClass = keyIteratorClass.getSuperclass();
        final Field declaredField = identityHashMapIteratorClass.getDeclaredField(fieldName);
        declaredField.setAccessible(true);
        return (Integer) declaredField.get(keyIterator);
    }

    /**
     * Get the private traversalTable field from the IdentityHashMap$KeyIterator inner
     * class, using reflection.
     *
     * @param keyIterator an instance of the IdentityHashMap$KeyIterator
     * @return the requested traversalTable, or {@code null} if it is not instantiated
     * @throws NoSuchFieldException   if the field traversalTable does not exist
     * @throws IllegalAccessException if it was not possible to get access to the field
     * @throws NoSuchClassException   if the inner class KeyIterator does not exist
     */
    private Object[] getTraversalTableFromKeyIterator(Iterator<?> keyIterator)
            throws NoSuchFieldException, IllegalAccessException, NoSuchClassException {
        final Class<?> keyIteratorClass = getInnerClass("KeyIterator");
        final Class<?> identityHashMapIteratorClass = keyIteratorClass.getSuperclass();
        final Field traversalTableField = identityHashMapIteratorClass.getDeclaredField("traversalTable");
        traversalTableField.setAccessible(true);
        return (Object[]) traversalTableField.get(keyIterator);
    }

    /**
     * Get the declared innerclass of the {@link IdentityHashMap} with the specified name,
     * using reflection.
     *
     * @param innerClassName the (Short) name of the inner {@link Class} to get from the
     *                       {@link IdentityHashMap} class
     * @return the requested inner class
     * @throws NoClassDefFoundError if the inner class does not exist
     */
    private Class<?> getInnerClass(String innerClassName)
            throws NoSuchClassException {
        return getInnerClass(IdentityHashMap.class, innerClassName);
    }

    /**
     * Get the declared innerclass of the specified outer class with the specified
     * inner class name, using reflection.
     *
     * @param outerClass     the outer class to search in
     * @param innerClassName the (short) name of the requested inner class
     * @return the requested inner class
     * @throws NoSuchClassException if the inner class does not exist
     */
    private Class<?> getInnerClass(Class<?> outerClass, String innerClassName)
            throws NoSuchClassException {
        final String searchName = String.format("%s$%s", outerClass.getName(), innerClassName);
        for (Class<?> clazz : outerClass.getDeclaredClasses()) {
            if (clazz.getName().equals(searchName)) return clazz;
        }
        throw new NoSuchClassException("Class " + innerClassName +
                " does not exist in " + outerClass.getName() + ".");
    }

    /**
     * Determines whether n is a power of two.
     *
     * @param n the value to probe
     * @return {@code true} if n is a power of two, or {@code false} otherwise.
     */
    private boolean isPowerOfTwo(int n) {
        return n > 0 && ((n & (n - 1)) == 0);
    }

    /**
     * An exception to be thrown when a class definition is not found, typically after
     * a failed attempt to find a class in the list resulting from a call to the method
     * {@link Class#getDeclaredClasses()}
     */
    private static class NoSuchClassException extends ReflectiveOperationException {
        NoSuchClassException(String msg) {
            super(msg);
        }
    }
}
