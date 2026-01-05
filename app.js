import * as THREE from 'three';
import { OrbitControls } from 'three/addons/controls/OrbitControls.js';
import * as zarr from 'zarrita';
import * as d3 from 'd3';
import { TabulatorFull as Tabulator } from 'tabulator-tables';

// Zarr file path
const ZARR_PATH = 'https://raw.githubusercontent.com/JEFworks-Lab/CellCarto-OvulationSlideseq/refs/heads/main/adata_ovary_combined_fullprocessed_annotated_withglobalspatial.zarr';

// Sparse matrix data (loaded once, used for gene lookups)
let sparseMatrix = {
    indptr: null,   // Int32Array - row pointers
    indices: null,  // Int32Array - column indices  
    data: null,     // Float32Array - values
    shape: null,    // [n_cells, n_genes]
    geneNames: null // Array of gene names (from var index)
};

// Gene statistics table
let geneTable = null;
let geneStats = [];

// Global gene selection function (set by setupGeneAutocomplete)
let selectGeneGlobal = null;

// Configuration for downsampling
const MAX_POINTS = 1000000; // Reduced for sphere rendering performance
    
// Coordinate configuration - will be populated dynamically
let availableCoordinateSources = {
    obs: [],  // Columns from obs (e.g., 'x', 'y', 'global_x', 'global_y', 'global_z')
    obsm: []  // Embeddings from obsm (e.g., 'Global_Spatial', 'X_pca', 'X_umap')
};

// Selected coordinate columns for x, y, and z
let selectedXCoord = null;  // Format: 'obs:column_name' or 'obsm:embedding_name:column_index'
let selectedYCoord = null;
let selectedZCoord = null;  // Can be null for "None"

// These will be populated from the zarr obs columns
let column_names_categorical = [];
let column_names_continuous = [];

// Global variables
let scene, camera, renderer, controls;
let points, pointCloud, sphereMesh;
let allData = [];
let visibleIndices = null; // Will be Uint32Array
let colorMap = new Map();
let attributeValues = {}; // Will be dynamically populated
let continuousRanges = {}; // Will store min/max for each continuous variable
let cameraInitialized = false;
let activeFilters = []; // Array of filter objects: { attribute, type: 'categorical'|'time', values/range }
let initialCameraState = { position: null, target: null }; // Store initial camera state for reset
let renderedIndicesMap = null; // Map from instance index to data index for hover detection
let highlightSphere = null; // Sphere to highlight hovered point
let tooltip = null; // Tooltip element
let isShiftPressed = false; // Track SHIFT key state
let raycaster = new THREE.Raycaster(); // For point picking
let mouse = new THREE.Vector2(); // Mouse position for raycasting
let selectedGene = null; // Currently selected gene for coloring

// Initialize Three.js scene
function initScene() {
    const container = document.getElementById('center-panel');
    const canvas = document.getElementById('scene');
    
    // Scene
    scene = new THREE.Scene();
    scene.background = new THREE.Color(0x1a1a1a);
    
    // Camera
    const width = container.clientWidth;
    const height = container.clientHeight;
    camera = new THREE.PerspectiveCamera(75, width / height, 0.1, 100000);
    camera.position.set(0, 0, 100);
    
    // Renderer
    renderer = new THREE.WebGLRenderer({ canvas: canvas, antialias: true });
    renderer.setSize(width, height);
    renderer.setPixelRatio(window.devicePixelRatio);
    
    // Controls
    controls = new OrbitControls(camera, renderer.domElement);
    controls.enableDamping = true;
    controls.dampingFactor = 0.05;
    controls.minDistance = 1;
    controls.maxDistance = 100000;
    // Completely disable OrbitControls pan and rotate - we'll handle it custom
    controls.enableRotate = false;
    controls.enablePan = false; // We'll handle panning manually
    controls.enableZoom = true; // Enable zooming (mouse wheel)
    controls.screenSpacePanning = false;
    controls.panSpeed = 1.0; // Pan speed reference
    
    // Disable OrbitControls mouse/touch handlers by overriding them
    controls.mouseButtons = {
        LEFT: null,  // Disable left mouse button
        MIDDLE: null, // Disable middle mouse button
        RIGHT: null  // Disable right mouse button
    };
    
    // Disable touch controls
    controls.touches = {
        ONE: null,
        TWO: null
    };
    
    // Track Control key state and mouse state
    let isControlPressed = false;
    let isDragging = false;
    let lastMousePosition = new THREE.Vector2();
    const panSpeed = 0.1; // Pan speed multiplier (increased for better responsiveness)
    const rotationSpeed = 0.01; // Rotation speed (increased for better responsiveness)
    
    // Listen for Control key
    window.addEventListener('keydown', (event) => {
        if (event.key === 'Control' || event.ctrlKey) {
            if (!isControlPressed) {
                isControlPressed = true;
                console.log('[Camera Controls] Control key pressed - rotation mode enabled');
            }
        }
    });
    
    window.addEventListener('keyup', (event) => {
        if (event.key === 'Control' || !event.ctrlKey) {
            if (isControlPressed) {
                isControlPressed = false;
                console.log('[Camera Controls] Control key released - pan mode enabled');
            }
        }
    });
    
    // Custom mouse handling for panning and rotation
    const canvasElement = renderer.domElement;
    
    if (!canvasElement) {
        console.error('[Camera Controls] ERROR: Canvas element not found!');
        return;
    }
    
    console.log('[Camera Controls] Setting up event listeners on canvas:', {
        canvasElement: canvasElement,
        canvasId: canvasElement.id,
        canvasTag: canvasElement.tagName,
        canvasClasses: canvasElement.className,
        parentElement: canvasElement.parentElement?.id || 'none'
    });
    
    // Use pointer events (better for Mac trackpads) and mouse events as fallback
    const handlePointerDown = (event) => {
        // Only handle if clicking on canvas or its children
        const target = event.target;
        if (!canvasElement.contains(target) && target !== canvasElement) {
            return;
        }
        
        console.log('[Camera Controls] pointerdown/mousedown event:', {
            type: event.type,
            pointerId: event.pointerId,
            button: event.button,
            buttons: event.buttons,
            clientX: event.clientX,
            clientY: event.clientY,
            isControlPressed: isControlPressed,
            ctrlKey: event.ctrlKey,
            metaKey: event.metaKey,
            target: target?.tagName,
            targetId: target?.id
        });
        
        // Accept any pointer/mouse down on the canvas (Mac trackpads work with pointer events)
        if (event.button === 0 || event.button === 2 || event.buttons > 0 || event.pointerType === 'mouse' || event.pointerType === 'touch') {
            event.preventDefault();
            event.stopPropagation();
            event.stopImmediatePropagation();
            isDragging = true;
            lastMousePosition.set(event.clientX, event.clientY);
            console.log('[Camera Controls] Dragging started, mode:', isControlPressed ? 'ROTATE' : 'PAN');
        }
    };
    
    // Add both pointer and mouse events for maximum compatibility
    canvasElement.addEventListener('pointerdown', handlePointerDown, { capture: true, passive: false });
    canvasElement.addEventListener('mousedown', handlePointerDown, { capture: true, passive: false });
    
    // Document-level fallback only for canvas events (use capture: false to not intercept other elements)
    document.addEventListener('pointerdown', (event) => {
        if (canvasElement.contains(event.target) || event.target === canvasElement) {
            handlePointerDown(event);
        }
    }, { capture: false, passive: false });
    
    document.addEventListener('mousedown', (event) => {
        if (canvasElement.contains(event.target) || event.target === canvasElement) {
            handlePointerDown(event);
        }
    }, { capture: false, passive: false });
    
    // Also handle touch events for Mac trackpads
    canvasElement.addEventListener('touchstart', (event) => {
        console.log('[Camera Controls] touchstart event:', {
            touches: event.touches.length,
            clientX: event.touches[0]?.clientX,
            clientY: event.touches[0]?.clientY,
            isControlPressed: isControlPressed
        });
        
        if (event.touches.length === 1) { // Single finger touch
            event.preventDefault();
            event.stopPropagation();
            event.stopImmediatePropagation();
            isDragging = true;
            lastMousePosition.set(event.touches[0].clientX, event.touches[0].clientY);
            console.log('[Camera Controls] Touch dragging started, mode:', isControlPressed ? 'ROTATE' : 'PAN');
        }
    }, { capture: true, passive: false });
    
    const handlePointerMove = (event) => {
        if (isDragging) {
            event.preventDefault();
            event.stopPropagation();
            event.stopImmediatePropagation();
            const deltaX = event.clientX - lastMousePosition.x;
            const deltaY = event.clientY - lastMousePosition.y;
            
            console.log('[Camera Controls] mousemove while dragging:', {
                deltaX: deltaX.toFixed(2),
                deltaY: deltaY.toFixed(2),
                isControlPressed: isControlPressed,
                mode: isControlPressed ? 'ROTATE' : 'PAN'
            });
            
            if (isControlPressed) {
                // Control + drag: Rotate camera
                // Up/down: rotate around x-axis (pitch) to view z variation
                // Left/right: rotate around y-axis (yaw)
                
                console.log('[Camera Controls] ROTATING - Control held');
                
                // Get camera's current position relative to target
                const offset = new THREE.Vector3();
                offset.subVectors(camera.position, controls.target);
                
                const beforePos = camera.position.clone();
                
                // Apply rotations
                if (Math.abs(deltaY) > 0) {
                    // Rotate around world x-axis (pitch) - tilt to see z variation
                    const pitchAngle = deltaY * rotationSpeed;
                    console.log('[Camera Controls] Rotating around X-axis (pitch):', pitchAngle.toFixed(4));
                    const xAxis = new THREE.Vector3(1, 0, 0);
                    const rotationMatrixX = new THREE.Matrix4();
                    rotationMatrixX.makeRotationAxis(xAxis, pitchAngle);
                    offset.applyMatrix4(rotationMatrixX);
                }
                
                if (Math.abs(deltaX) > 0) {
                    // Rotate around world y-axis (yaw)
                    const yawAngle = deltaX * rotationSpeed;
                    console.log('[Camera Controls] Rotating around Y-axis (yaw):', yawAngle.toFixed(4));
                    const yAxis = new THREE.Vector3(0, 1, 0);
                    const rotationMatrixY = new THREE.Matrix4();
                    rotationMatrixY.makeRotationAxis(yAxis, yawAngle);
                    offset.applyMatrix4(rotationMatrixY);
                }
                
                // Update camera position
                camera.position.copy(controls.target).add(offset);
                
                // Update camera to look at target
                camera.lookAt(controls.target);
                
                console.log('[Camera Controls] Camera position updated:', {
                    before: `(${beforePos.x.toFixed(2)}, ${beforePos.y.toFixed(2)}, ${beforePos.z.toFixed(2)})`,
                    after: `(${camera.position.x.toFixed(2)}, ${camera.position.y.toFixed(2)}, ${camera.position.z.toFixed(2)})`
                });
            } else {
                // Default drag: Pan camera in x-y plane
                // Up/down: pan in y direction (world space)
                // Left/right: pan in x direction (world space)
                
                console.log('[Camera Controls] PANNING - No Control key');
                
                // Scale pan speed by camera distance for more natural feel
                const cameraDistance = camera.position.distanceTo(controls.target);
                const scaledPanSpeed = panSpeed * (cameraDistance * 0.01);
                
                const beforeTarget = controls.target.clone();
                const beforePos = camera.position.clone();
                
                if (Math.abs(deltaY) > 0) {
                    // Pan in y direction (world space)
                    const yPanAmount = deltaY * scaledPanSpeed;
                    console.log('[Camera Controls] Panning in Y direction:', yPanAmount.toFixed(4));
                    const yPanVector = new THREE.Vector3(0, yPanAmount, 0);
                    controls.target.add(yPanVector);
                    camera.position.add(yPanVector);
                }
                
                if (Math.abs(deltaX) > 0) {
                    // Pan in x direction (world space)
                    const xPanAmount = deltaX * scaledPanSpeed;
                    console.log('[Camera Controls] Panning in X direction:', xPanAmount.toFixed(4));
                    const xPanVector = new THREE.Vector3(xPanAmount, 0, 0);
                    controls.target.add(xPanVector);
                    camera.position.add(xPanVector);
                }
                
                console.log('[Camera Controls] Target updated:', {
                    before: `(${beforeTarget.x.toFixed(2)}, ${beforeTarget.y.toFixed(2)}, ${beforeTarget.z.toFixed(2)})`,
                    after: `(${controls.target.x.toFixed(2)}, ${controls.target.y.toFixed(2)}, ${controls.target.z.toFixed(2)})`
                });
            }
            
            controls.update();
            camera.updateMatrixWorld();
            lastMousePosition.set(event.clientX, event.clientY);
        }
    };
    
    // Add both pointer and mouse events
    canvasElement.addEventListener('pointermove', handlePointerMove, { capture: true, passive: false });
    canvasElement.addEventListener('mousemove', handlePointerMove, { capture: true, passive: false });
    
    // Document-level fallback for dragging outside canvas (use capture: false)
    document.addEventListener('pointermove', (event) => {
        if (isDragging) {
            handlePointerMove(event);
        }
    }, { capture: false, passive: true });
    
    document.addEventListener('mousemove', (event) => {
        if (isDragging) {
            handlePointerMove(event);
        }
    }, { capture: false, passive: true });
    
    // Handle touchmove for Mac trackpads
    canvasElement.addEventListener('touchmove', (event) => {
        if (isDragging && event.touches.length === 1) {
            event.preventDefault();
            event.stopPropagation();
            event.stopImmediatePropagation();
            const deltaX = event.touches[0].clientX - lastMousePosition.x;
            const deltaY = event.touches[0].clientY - lastMousePosition.y;
            
            console.log('[Camera Controls] touchmove while dragging:', {
                deltaX: deltaX.toFixed(2),
                deltaY: deltaY.toFixed(2),
                isControlPressed: isControlPressed,
                mode: isControlPressed ? 'ROTATE' : 'PAN'
            });
            
            // Use the same logic as mousemove
            if (isControlPressed) {
                // Rotate logic (same as mousemove)
                const offset = new THREE.Vector3();
                offset.subVectors(camera.position, controls.target);
                
                if (Math.abs(deltaY) > 0) {
                    const pitchAngle = deltaY * rotationSpeed;
                    const xAxis = new THREE.Vector3(1, 0, 0);
                    const rotationMatrixX = new THREE.Matrix4();
                    rotationMatrixX.makeRotationAxis(xAxis, pitchAngle);
                    offset.applyMatrix4(rotationMatrixX);
                }
                
                if (Math.abs(deltaX) > 0) {
                    const yawAngle = deltaX * rotationSpeed;
                    const yAxis = new THREE.Vector3(0, 1, 0);
                    const rotationMatrixY = new THREE.Matrix4();
                    rotationMatrixY.makeRotationAxis(yAxis, yawAngle);
                    offset.applyMatrix4(rotationMatrixY);
                }
                
                camera.position.copy(controls.target).add(offset);
                camera.lookAt(controls.target);
            } else {
                // Pan logic (same as mousemove)
                const cameraDistance = camera.position.distanceTo(controls.target);
                const scaledPanSpeed = panSpeed * (cameraDistance * 0.01);
                
                if (Math.abs(deltaY) > 0) {
                    const yPanAmount = deltaY * scaledPanSpeed;
                    const yPanVector = new THREE.Vector3(0, yPanAmount, 0);
                    controls.target.add(yPanVector);
                    camera.position.add(yPanVector);
                }
                
                if (Math.abs(deltaX) > 0) {
                    const xPanAmount = deltaX * scaledPanSpeed;
                    const xPanVector = new THREE.Vector3(xPanAmount, 0, 0);
                    controls.target.add(xPanVector);
                    camera.position.add(xPanVector);
                }
            }
            
            controls.update();
            camera.updateMatrixWorld();
            lastMousePosition.set(event.touches[0].clientX, event.touches[0].clientY);
        }
    }, { capture: true, passive: false });
    
    const handlePointerUp = (event) => {
        console.log('[Camera Controls] pointerup/mouseup event:', {
            type: event.type,
            button: event.button,
            buttons: event.buttons,
            isDragging: isDragging,
            pointerId: event.pointerId
        });
        
        if (isDragging) {
            event.preventDefault();
            event.stopPropagation();
            event.stopImmediatePropagation();
            isDragging = false;
            console.log('[Camera Controls] Dragging stopped');
        }
    };
    
    // Add both pointer and mouse events on canvas
    canvasElement.addEventListener('pointerup', handlePointerUp, { capture: true, passive: false });
    canvasElement.addEventListener('mouseup', handlePointerUp, { capture: true, passive: false });
    
    // Document-level listeners only handle events when dragging (for drag release outside canvas)
    document.addEventListener('pointerup', (event) => {
        if (isDragging) {
            handlePointerUp(event);
        }
    }, { capture: false, passive: true });
    document.addEventListener('mouseup', (event) => {
        if (isDragging) {
            handlePointerUp(event);
        }
    }, { capture: false, passive: true });
    
    // Handle touchend for Mac trackpads
    canvasElement.addEventListener('touchend', (event) => {
        console.log('[Camera Controls] touchend event');
        event.preventDefault();
        event.stopPropagation();
        event.stopImmediatePropagation();
        isDragging = false;
        console.log('[Camera Controls] Touch dragging stopped');
    }, { capture: true, passive: false });
    
    // Handle pointer cancel (Mac trackpads sometimes send this)
    canvasElement.addEventListener('pointercancel', (event) => {
        console.log('[Camera Controls] pointercancel event');
        isDragging = false;
    }, { capture: true, passive: false });
    
    canvasElement.addEventListener('mouseleave', () => {
        if (isDragging) {
            console.log('[Camera Controls] Mouse left canvas while dragging - stopping drag');
            isDragging = false;
        }
    });
    
    canvasElement.addEventListener('pointerleave', () => {
        if (isDragging) {
            console.log('[Camera Controls] Pointer left canvas while dragging - stopping drag');
            isDragging = false;
        }
    });
    
    // Test listener to see if ANY events are being received on the canvas
    const testAllEvents = ['click', 'mousedown', 'pointerdown', 'touchstart', 'contextmenu'];
    testAllEvents.forEach(eventType => {
        canvasElement.addEventListener(eventType, (event) => {
            console.log(`[Camera Controls] TEST - ${eventType} event received on canvas:`, {
                type: event.type,
                target: event.target?.tagName,
                button: event.button,
                buttons: event.buttons
            });
        }, { capture: true });
    });
    
    // Also handle mouseup on window to catch cases where mouse is released outside canvas
    window.addEventListener('mouseup', (event) => {
        if (event.button === 0 || event.button === 2) {
            if (isDragging) {
                console.log('[Camera Controls] Mouse released outside canvas - stopping drag');
                isDragging = false;
            }
        }
    });
    
    // Add initial state logging
    console.log('[Camera Controls] Initialized:', {
        enableRotate: controls.enableRotate,
        enablePan: controls.enablePan,
        enableZoom: controls.enableZoom,
        canvasElement: canvasElement ? 'found' : 'NOT FOUND'
    });
    
    // Prevent context menu on right click when Control is held
    canvasElement.addEventListener('contextmenu', (event) => {
        if (isControlPressed) {
            event.preventDefault();
        }
    });
    
    // Lighting
    const ambientLight = new THREE.AmbientLight(0xffffff, 0.6);
    scene.add(ambientLight);
    
    const directionalLight = new THREE.DirectionalLight(0xffffff, 0.4);
    directionalLight.position.set(1, 1, 1);
    scene.add(directionalLight);
    
    // Handle window resize
    window.addEventListener('resize', onWindowResize);
    
    // Track SHIFT key for hover highlighting
    window.addEventListener('keydown', (event) => {
        if (event.key === 'Shift' || event.shiftKey) {
            if (!isShiftPressed) {
                isShiftPressed = true;
                console.log('[Hover] SHIFT pressed - hover mode enabled');
            }
        }
    });
    
    window.addEventListener('keyup', (event) => {
        if (event.key === 'Shift' || !event.shiftKey) {
            if (isShiftPressed) {
                isShiftPressed = false;
                console.log('[Hover] SHIFT released - hover mode disabled');
                // Hide highlight and tooltip when SHIFT is released
                hideHighlight();
            }
        }
    });
    
    // Create tooltip element
    tooltip = document.createElement('div');
    tooltip.id = 'point-tooltip';
    tooltip.style.cssText = `
        position: fixed;
        background: rgba(0, 0, 0, 0.9);
        color: white;
        padding: 8px 12px;
        border-radius: 4px;
        font-size: 12px;
        pointer-events: none;
        z-index: 10000;
        border: 1px solid rgba(255, 255, 255, 0.3);
        display: none;
        max-width: 300px;
        line-height: 1.4;
        box-shadow: 0 4px 6px rgba(0, 0, 0, 0.5);
    `;
    document.body.appendChild(tooltip);
    console.log('[Hover] Tooltip element created');
    
    // Create highlight sphere (will be positioned dynamically)
    // Use a slightly larger sphere with wireframe for white border effect
    const highlightGeometry = new THREE.SphereGeometry(1, 16, 16);
    const highlightMaterial = new THREE.MeshBasicMaterial({
        color: 0xffffff,
        transparent: false,
        opacity: 1.0,
        wireframe: true,
        side: THREE.DoubleSide,
        depthTest: true,
        depthWrite: false // Don't write to depth buffer
    });
    highlightSphere = new THREE.Mesh(highlightGeometry, highlightMaterial);
    highlightSphere.renderOrder = 1000; // Render on top
    highlightSphere.visible = false;
    scene.add(highlightSphere);
    
    console.log('[Hover] Highlight sphere created and added to scene');
    
    // Add mouse move handler for hover detection (reuse canvasElement from above)
    const hoverCanvasElement = renderer.domElement;
    hoverCanvasElement.addEventListener('mousemove', handleHover, { passive: true });
    hoverCanvasElement.addEventListener('pointermove', handleHover, { passive: true });
    
    // Keep loading message visible initially (will be hidden after data loads)
}

function onWindowResize() {
    const container = document.getElementById('center-panel');
    const width = container.clientWidth;
    const height = container.clientHeight;
    
    camera.aspect = width / height;
    camera.updateProjectionMatrix();
    renderer.setSize(width, height);
}

// Handle hover detection when SHIFT is held
function handleHover(event) {
    // Only handle hover if SHIFT is pressed and not dragging camera
    if (!isShiftPressed || !sphereMesh || !renderedIndicesMap) {
        hideHighlight();
        return;
    }
    
    // Don't interfere with camera controls - check if mouse buttons are pressed
    if (event.buttons && event.buttons > 0) {
        // User is dragging, don't show hover
        hideHighlight();
        return;
    }
    
    const canvas = renderer.domElement;
    const rect = canvas.getBoundingClientRect();
    
    // Calculate mouse position in normalized device coordinates (-1 to +1)
    mouse.x = ((event.clientX - rect.left) / rect.width) * 2 - 1;
    mouse.y = -((event.clientY - rect.top) / rect.height) * 2 + 1;
    
    // Update raycaster - for instanced meshes, we need to check intersections properly
    const pointSize = parseFloat(document.getElementById('pointSize')?.value || 1);
    raycaster.setFromCamera(mouse, camera);
    
    // Check intersection with instanced mesh
    // Note: Raycaster should automatically handle instanced meshes
    try {
        const intersects = raycaster.intersectObject(sphereMesh, false);
        
        if (intersects.length > 0) {
            const intersection = intersects[0];
            const instanceId = intersection.instanceId;
            
            if (instanceId !== undefined && instanceId !== null && instanceId < renderedIndicesMap.length) {
                const dataIdx = renderedIndicesMap[instanceId];
                if (dataIdx !== undefined && dataIdx < allData.length) {
                    const point = allData[dataIdx];
                    
                    // Show highlight at the actual point position (not intersection point)
                    const pointPosition = new THREE.Vector3(point.x, point.y, point.z);
                    showHighlight(pointPosition, point, event.clientX, event.clientY);
                    
                    // Log for debugging (only occasionally to avoid spam)
                    if (Math.random() < 0.01) { // Log 1% of the time
                        console.log('[Hover] Point highlighted:', {
                            instanceId,
                            dataIdx,
                            position: `(${point.x.toFixed(2)}, ${point.y.toFixed(2)}, ${point.z.toFixed(2)})`
                        });
                    }
                } else {
                    hideHighlight();
                }
            } else {
                hideHighlight();
            }
        } else {
            hideHighlight();
        }
    } catch (error) {
        console.warn('[Hover] Error in raycasting:', error);
        hideHighlight();
    }
}

// Show highlight and tooltip for a point
function showHighlight(position, point, mouseX, mouseY) {
    if (!highlightSphere || !tooltip) {
        console.warn('[Hover] Highlight sphere or tooltip not available');
        return;
    }
    
    // Show and position highlight sphere
    const pointSize = parseFloat(document.getElementById('pointSize')?.value || 1);
    // Make highlight 1.5x the point size for visibility
    const highlightScale = pointSize * 1.5;
    highlightSphere.scale.set(highlightScale, highlightScale, highlightScale);
    highlightSphere.position.copy(position);
    highlightSphere.visible = true;
    
    // Create tooltip content
    const colorBy = document.getElementById('colorBy')?.value || 'gene';
    let tooltipContent = '<div style="font-weight: bold; margin-bottom: 6px; border-bottom: 1px solid rgba(255,255,255,0.3); padding-bottom: 4px;">Point Information</div>';
    
    // Add coordinates
    tooltipContent += `<div style="margin-bottom: 4px;"><strong>Coordinates:</strong><br>(${point.x.toFixed(2)}, ${point.y.toFixed(2)}, ${point.z.toFixed(2)})</div>`;
    
    // Add all categorical attributes
    column_names_categorical.forEach(col => {
        if (point[col] !== undefined && point[col] !== '') {
            tooltipContent += `<div style="margin-bottom: 2px;"><strong>${col}:</strong> ${point[col]}</div>`;
        }
    });
    
    // Add all continuous attributes
    column_names_continuous.forEach(col => {
        if (point[col] !== null && point[col] !== undefined) {
            tooltipContent += `<div style="margin-bottom: 2px;"><strong>${col}:</strong> ${point[col].toFixed(4)}</div>`;
        }
    });
    
    tooltip.innerHTML = tooltipContent;
    tooltip.style.display = 'block';
    
    // Position tooltip near mouse cursor
    const offset = 15;
    tooltip.style.left = (mouseX + offset) + 'px';
    tooltip.style.top = (mouseY + offset) + 'px';
    
    // Adjust if tooltip goes off screen
    requestAnimationFrame(() => {
        const tooltipRect = tooltip.getBoundingClientRect();
        const windowWidth = window.innerWidth;
        const windowHeight = window.innerHeight;
        
        if (tooltipRect.right > windowWidth) {
            tooltip.style.left = (mouseX - tooltipRect.width - offset) + 'px';
        }
        if (tooltipRect.bottom > windowHeight) {
            tooltip.style.top = (mouseY - tooltipRect.height - offset) + 'px';
        }
        if (tooltipRect.left < 0) {
            tooltip.style.left = offset + 'px';
        }
        if (tooltipRect.top < 0) {
            tooltip.style.top = offset + 'px';
        }
    });
}

// Hide highlight and tooltip
function hideHighlight() {
    if (highlightSphere) {
        highlightSphere.visible = false;
    }
    if (tooltip) {
        tooltip.style.display = 'none';
    }
}

// Global zarr root for gene loading
let zarrRoot = null;

// Cached zarr arrays for efficient repeated gene loading (CSR format)
let cachedZarrArrays = null;

// Column metadata (stored without loading data)
let columnMetadata = {}; // Maps column name to { type: 'categorical'|'continuous', encodingType: string, path: string }

// Track which columns have been loaded
let loadedColumns = new Set();

// Base URL for zarr store
let zarrBaseUrl = null;

// Var column metadata (stored without loading data)
let varColumnMetadata = {}; // Maps column name to { encodingType: string, path: string }

// Track which var columns have been loaded
let varColumnsLoaded = false;

/**
 * Helper function to decode categorical columns (codes + categories)
 */
async function loadCategoricalColumn(root, basePath) {
    const codesArr = await zarr.open(root.resolve(`${basePath}/codes`), { kind: 'array' });
    const catsArr = await zarr.open(root.resolve(`${basePath}/categories`), { kind: 'array' });
    
    const codes = await zarr.get(codesArr);
    const categories = await zarr.get(catsArr);
    
    // Map codes to category values
    const result = new Array(codes.data.length);
    for (let i = 0; i < codes.data.length; i++) {
        result[i] = categories.data[codes.data[i]];
    }
    return result;
}

/**
 * Load a zarr array and return its data
 */
async function loadZarrArray(root, path) {
    try {
        const arr = await zarr.open(root.resolve(path), { kind: 'array' });
        const data = await zarr.get(arr);
        return data;
    } catch (error) {
        console.error(`[loadZarrArray] Error loading ${path}:`, error);
        throw error;
    }
}

/**
 * Lazily load an obs column if not already loaded
 */
async function ensureColumnLoaded(colName) {
    if (loadedColumns.has(colName)) {
        return; // Already loaded
    }
    
    if (!zarrRoot || !columnMetadata[colName]) {
        console.warn(`[ensureColumnLoaded] Cannot load column ${colName}: metadata not available`);
        return;
    }
    
    console.log(`[ensureColumnLoaded] Loading column: ${colName}`);
    const metadata = columnMetadata[colName];
    const nCells = allData.length;
    
    try {
        let values;
        const isNumericData = metadata.type === 'continuous';
        
        if (metadata.encodingType === 'categorical') {
            // Categorical column - has codes/categories
            values = await loadCategoricalColumn(zarrRoot, `obs/${colName}`);
        } else {
            // Numeric or string array
            try {
                const colData = await loadZarrArray(zarrRoot, `obs/${colName}`);
                values = Array.from(colData.data);
            } catch (numError) {
                // Column has no data chunks (e.g., all zeros were optimized away)
                console.log(`[ensureColumnLoaded] ${colName} has no data, filling with zeros`);
                values = new Array(nCells).fill(isNumericData ? 0 : '');
            }
        }
        
        // Store values in allData
        if (isNumericData) {
            // Process as numeric
            if (!continuousRanges[colName]) {
                continuousRanges[colName] = { min: Infinity, max: -Infinity };
            }
            const range = continuousRanges[colName];
            
            for (let i = 0; i < nCells; i++) {
                const rawVal = values[i];
                const val = typeof rawVal === 'number' ? rawVal : parseFloat(rawVal);
                allData[i][colName] = val;
                if (!isNaN(val)) {
                    range.min = Math.min(range.min, val);
                    range.max = Math.max(range.max, val);
                }
            }
            console.log(`[ensureColumnLoaded] Loaded numeric column ${colName}: range [${range.min.toFixed(2)}, ${range.max.toFixed(2)}]`);
        } else {
            // Process as categorical
            if (!attributeValues[colName]) {
                attributeValues[colName] = new Set();
            }
            const attrValues = attributeValues[colName];
            
            for (let i = 0; i < nCells; i++) {
                const val = String(values[i] || '');
                allData[i][colName] = val;
                if (val) {
                    attrValues.add(val);
                }
            }
            console.log(`[ensureColumnLoaded] Loaded categorical column ${colName}: ${attrValues.size} unique values`);
        }
        
        loadedColumns.add(colName);
    } catch (error) {
        console.error(`[ensureColumnLoaded] Error loading column ${colName}:`, error);
        // Fill with defaults
        for (let i = 0; i < nCells; i++) {
            allData[i][colName] = isNumericData ? 0 : '';
        }
        loadedColumns.add(colName); // Mark as loaded to avoid repeated failures
    }
}

/**
 * Ensure multiple columns are loaded (for filters, legend, etc.)
 */
async function ensureColumnsLoaded(colNames) {
    const toLoad = colNames.filter(col => !loadedColumns.has(col));
    if (toLoad.length === 0) {
        return;
    }
    
    console.log(`[ensureColumnsLoaded] Loading ${toLoad.length} columns: ${toLoad.join(', ')}`);
    
    // Load columns sequentially to avoid overwhelming the browser
    for (const colName of toLoad) {
        await ensureColumnLoaded(colName);
        // Small delay to allow UI updates
        await new Promise(resolve => setTimeout(resolve, 10));
    }
}

/**
 * Load all var columns (lazy loading for gene statistics table)
 */
async function ensureVarColumnsLoaded() {
    if (varColumnsLoaded) {
        return; // Already loaded
    }
    
    if (!zarrRoot || !sparseMatrix.geneNames || Object.keys(varColumnMetadata).length === 0) {
        console.warn('[ensureVarColumnsLoaded] Cannot load var columns: metadata not available');
        return;
    }
    
    console.log('[ensureVarColumnsLoaded] Loading var columns...');
    const varColumnOrder = Object.keys(varColumnMetadata);
    const nGenes = sparseMatrix.geneNames.length;
    
    const varColumnData = {};
    const varColumnTypes = {};
    
    for (const colName of varColumnOrder) {
        try {
            const metadata = varColumnMetadata[colName];
            const isCategorical = metadata.encodingType === 'categorical';
            
            if (isCategorical) {
                // Load categorical column
                const catData = await loadCategoricalColumn(zarrRoot, `var/${colName}`);
                varColumnData[colName] = catData;
                varColumnTypes[colName] = 'categorical';
            } else {
                // Load numeric column
                const colData = await loadZarrArray(zarrRoot, `var/${colName}`);
                varColumnData[colName] = Array.from(colData.data);
                varColumnTypes[colName] = 'numeric';
            }
        } catch (colError) {
            console.warn(`[ensureVarColumnsLoaded] Could not load var column ${colName}:`, colError);
        }
    }
    
    // Build gene stats array with all var columns
    // Normalize field names by replacing dots with underscores (Tabulator interprets dots as nested paths)
    geneStats = sparseMatrix.geneNames.map((name, i) => {
        const stats = { gene: name };
        // Add all var columns, normalizing field names
        for (const colName of varColumnOrder) {
            // Replace dots with underscores in field names to avoid Tabulator nested path issues
            const normalizedFieldName = colName.replace(/\./g, '_');
            if (varColumnData[colName] && varColumnData[colName][i] !== undefined) {
                stats[normalizedFieldName] = varColumnData[colName][i];
            } else {
                stats[normalizedFieldName] = null;
            }
        }
        return stats;
    });
    
    // Store mapping from normalized names to original names for display
    const fieldNameMapping = {};
    for (const colName of varColumnOrder) {
        const normalized = colName.replace(/\./g, '_');
        fieldNameMapping[normalized] = colName;
    }
    // Store mapping globally for use in table initialization
    window.varFieldNameMapping = fieldNameMapping;
    
    varColumnsLoaded = true;
    console.log(`[ensureVarColumnsLoaded] Loaded statistics for ${geneStats.length} genes with ${varColumnOrder.length} columns`);
}

/**
 * Discover available coordinate sources from obsm only
 * Note: obs columns are not used for coordinates, only obsm embeddings
 */
async function discoverCoordinateSources(root, baseUrl) {
    const sources = {
        obs: [],  // Not used for coordinates, but kept for potential future use
        obsm: []
    };
    
    // Note: We do NOT discover obs columns for coordinate selection
    // Only obsm embeddings are used for X and Y coordinates
    
    // Discover embeddings from obsm
    try {
        const obsmAttrsResponse = await fetch(`${baseUrl}/obsm/.zattrs`);
        if (obsmAttrsResponse.ok) {
            const obsmAttrs = await obsmAttrsResponse.json();
            
            // Try to list obsm directories
            // obsm typically contains embeddings like X_pca, X_umap, spatial, etc.
            // We need to check what's actually available
            try {
                // Comprehensive list of potential embedding names to check
                // This includes all common embedding types and the specific ones mentioned by user
                const potentialEmbeddings = [
                    'Global_Spatial',  // User mentioned
                    'spatial',         // User mentioned
                    'X_pca',          // User mentioned
                    'X_pca_harmony',  // User mentioned
                    'X_umap',         // User mentioned
                    'X_tsne',
                    'X_tsne_3d',
                    'X_umap_3d',
                    'X_pca_3d',
                    'pca',
                    'umap',
                    'tsne',
                    'harmony',
                    'X_harmony'
                ];
                
                // Try to discover embeddings by accessing obsm as a group
                // In zarr v2, groups might have metadata that lists children
                const discoveredEmbeddings = new Set();
                
                // First, try to get a list from obsm group metadata if available
                try {
                    // Some zarr implementations store group children in .zattrs or .zgroup
                    // Try to access this information
                    const obsmGroupResponse = await fetch(`${baseUrl}/obsm/.zgroup`);
                    if (obsmGroupResponse.ok) {
                        // Group metadata might have children listed
                        // This is implementation-dependent, so we'll still check individual embeddings
                    }
                } catch (e) {
                    // Not available or not supported
                }
                
                // Check all potential embeddings
                for (const embName of potentialEmbeddings) {
                    try {
                        const embAttrsResponse = await fetch(`${baseUrl}/obsm/${embName}/.zattrs`);
                        if (embAttrsResponse.ok) {
                            discoveredEmbeddings.add(embName);
                            console.log(`[discoverCoordinateSources] Found embedding: ${embName}`);
                        }
                    } catch (e) {
                        // This embedding doesn't exist, skip
                    }
                }
                
                // Also try pattern-based discovery for common naming conventions
                // Try X_* patterns (X_pca, X_umap, etc.)
                const xPatterns = ['X_pca', 'X_umap', 'X_tsne', 'X_harmony', 'X_pca_harmony'];
                for (const pattern of xPatterns) {
                    if (!discoveredEmbeddings.has(pattern)) {
                        try {
                            const embAttrsResponse = await fetch(`${baseUrl}/obsm/${pattern}/.zattrs`);
                            if (embAttrsResponse.ok) {
                                discoveredEmbeddings.add(pattern);
                                console.log(`[discoverCoordinateSources] Found embedding via pattern: ${pattern}`);
                            }
                        } catch (e) {
                            // Doesn't exist
                        }
                    }
                }
                
                // Process all discovered embeddings
                for (const embName of discoveredEmbeddings) {
                    try {
                        const embAttrsResponse = await fetch(`${baseUrl}/obsm/${embName}/.zattrs`);
                        if (embAttrsResponse.ok) {
                            const embAttrs = await embAttrsResponse.json();
                            const encodingType = embAttrs['encoding-type'];
                            
                            if (encodingType === 'dataframe') {
                                // DataFrame format (like Global_Spatial) - has named columns
                                const columnOrder = embAttrs['column-order'] || [];
                                
                                columnOrder.forEach((colName, colIdx) => {
                                    sources.obsm.push({
                                        name: colName,
                                        displayName: `obsm:${embName}:${colName}`,
                                        source: 'obsm',
                                        embedding: embName,
                                        columnIndex: colIdx,
                                        columnName: colName
                                    });
                                });
                            } else {
                                // Array format (like X_pca, X_umap) - 2D array with dimensions
                                // Try to determine number of dimensions by opening the array
                                try {
                                    let maxDim = 0;
                                    
                                    // Try to open the array directly to get its shape
                                    try {
                                        const embArray = await zarr.open(root.resolve(`obsm/${embName}`), { kind: 'array' });
                                        const shape = embArray.shape;
                                        if (shape && shape.length === 2) {
                                            // It's a 2D array: [n_cells, n_dims]
                                            maxDim = shape[1];
                                            console.log(`[discoverCoordinateSources] Found ${embName} with shape [${shape[0]}, ${shape[1]}]`);
                                        } else if (shape && shape.length === 1) {
                                            // 1D array - just one dimension
                                            maxDim = 1;
                                            console.log(`[discoverCoordinateSources] Found ${embName} with shape [${shape[0]}]`);
                                        }
                                    } catch (e) {
                                        // Couldn't open as array, try to get shape from metadata
                                        try {
                                            const arrayPath = `${baseUrl}/obsm/${embName}/.zarray`;
                                            const arrayResponse = await fetch(arrayPath);
                                            if (arrayResponse.ok) {
                                                const arrayAttrs = await arrayResponse.json();
                                                const shape = arrayAttrs.shape || [];
                                                if (shape.length === 2) {
                                                    maxDim = shape[1];
                                                    console.log(`[discoverCoordinateSources] Found ${embName} shape from metadata: [${shape[0]}, ${shape[1]}]`);
                                                } else if (shape.length === 1) {
                                                    maxDim = 1;
                                                }
                                            }
                                        } catch (e2) {
                                            // Fall back to chunk-based discovery
                                            console.log(`[discoverCoordinateSources] Could not get shape for ${embName}, trying chunk discovery`);
                                        }
                                    }
                                    
                                    // If we still don't have dimensions, try chunk-based discovery
                                    if (maxDim === 0) {
                                        // Check for dimension chunks (format: dim0.dim1 where dim0 is column index)
                                        // We'll check up to 100 dimensions to be safe
                                        for (let dim = 0; dim < 100; dim++) {
                                            try {
                                                // Try to load a chunk to see if this dimension exists
                                                const testChunk = await zarr.open(root.resolve(`obsm/${embName}/${dim}.0`), { kind: 'array' });
                                                if (testChunk) {
                                                    maxDim = dim + 1;
                                                } else {
                                                    break;
                                                }
                                            } catch (e) {
                                                // This dimension doesn't exist, stop
                                                break;
                                            }
                                        }
                                    }
                                    
                                    // Add options for each dimension
                                    if (maxDim > 0) {
                                        // For coordinate visualization, we typically need 2 dimensions (x, y)
                                        // But show more options for flexibility (e.g., PCA might have 50+ components)
                                        // For most embeddings, show first 20 dimensions (enough for visualization)
                                        // For UMAP, typically only 2 dimensions, for PCA can be many
                                        const dimsToShow = Math.min(maxDim, 20);
                                        for (let dim = 0; dim < dimsToShow; dim++) {
                                            sources.obsm.push({
                                                name: `${embName}_dim${dim}`,
                                                displayName: `obsm:${embName}:dim${dim}`,
                                                source: 'obsm',
                                                embedding: embName,
                                                columnIndex: dim,
                                                columnName: null
                                            });
                                        }
                                        if (maxDim > dimsToShow) {
                                            console.log(`[discoverCoordinateSources] Added ${dimsToShow} of ${maxDim} dimensions for ${embName} (showing first ${dimsToShow} for UI)`);
                                        } else {
                                            console.log(`[discoverCoordinateSources] Added ${maxDim} dimensions for ${embName}`);
                                        }
                                    } else {
                                        console.warn(`[discoverCoordinateSources] Could not determine dimensions for ${embName}`);
                                    }
                                } catch (e) {
                                    console.warn(`[discoverCoordinateSources] Error determining dimensions for ${embName}:`, e);
                                }
                            }
                        }
                    } catch (e) {
                        console.warn(`[discoverCoordinateSources] Error processing embedding ${embName}:`, e);
                    }
                }
            } catch (e) {
                console.warn('[discoverCoordinateSources] Could not discover obsm embeddings:', e);
            }
        }
    } catch (e) {
        console.warn('[discoverCoordinateSources] Could not read obsm/.zattrs:', e);
    }
    
    console.log('[discoverCoordinateSources] Found coordinate sources:', sources);
    return sources;
}

/**
 * Load coordinate values from a coordinate source
 */
async function loadCoordinateValues(root, coordSource, nCells) {
    if (coordSource.source === 'obs') {
        // Load from obs column
        try {
            const colData = await loadZarrArray(root, `obs/${coordSource.path}`);
            return Array.from(colData.data);
        } catch (e) {
            console.warn(`[loadCoordinateValues] Could not load obs/${coordSource.path}:`, e);
            return new Array(nCells).fill(0);
        }
    } else if (coordSource.source === 'obsm') {
        // Load from obsm embedding
        try {
            const embName = coordSource.embedding;
            const colIdx = coordSource.columnIndex;
            
            // Try to load by column name first (for embeddings like Global_Spatial with named columns)
            if (coordSource.columnName) {
                try {
                    // For DataFrame-encoded embeddings, columns are stored as separate arrays
                    // Try loading as a zarr array directly
                    const colArray = await zarr.open(root.resolve(`obsm/${embName}/${coordSource.columnName}`), { kind: 'array' });
                    const colData = await zarr.get(colArray);
                    return Array.from(colData.data);
                } catch (e) {
                    // Fall through to index-based loading
                    console.log(`[loadCoordinateValues] Could not load by column name, trying index:`, e);
                }
            }
            
            // Load by dimension index
            // For 2D embeddings stored as arrays, dimensions are stored as colIdx.0, colIdx.1, etc. (chunks)
            // We need to load all chunks and concatenate them
            try {
                // Try loading as a 2D array first (more efficient)
                try {
                    const fullArray = await zarr.open(root.resolve(`obsm/${embName}`), { kind: 'array' });
                    // Get the shape to understand the structure
                    const shape = fullArray.shape;
                    if (shape && shape.length === 2) {
                        // It's a 2D array: [n_cells, n_dims]
                        // Extract the column we want
                        const colData = await zarr.get(fullArray, [zarr.slice(null, null), zarr.slice(colIdx, colIdx + 1)]);
                        // colData should be shape [n_cells, 1], flatten it
                        const result = new Array(shape[0]);
                        for (let i = 0; i < shape[0]; i++) {
                            result[i] = colData.data[i];
                        }
                        return result;
                    }
                } catch (e) {
                    // Not a simple 2D array, try chunk-based loading
                }
                
                // Chunk-based loading: load colIdx.0, colIdx.1, etc. and concatenate
                let result = [];
                let chunkIdx = 0;
                while (result.length < nCells) {
                    try {
                        const chunk = await loadZarrArray(root, `obsm/${embName}/${colIdx}.${chunkIdx}`);
                        result = result.concat(Array.from(chunk.data));
                        chunkIdx++;
                    } catch (e) {
                        // No more chunks
                        break;
                    }
                }
                
                // Return the result (truncate to nCells if needed)
                if (result.length >= nCells) {
                    return result.slice(0, nCells);
                } else if (result.length > 0) {
                    // Pad with zeros if needed
                    while (result.length < nCells) {
                        result.push(0);
                    }
                    return result;
                }
                
                throw new Error('Could not load any chunks');
            } catch (e) {
                console.warn(`[loadCoordinateValues] Could not load obsm/${embName} dimension ${colIdx}:`, e);
                return new Array(nCells).fill(0);
            }
        } catch (e) {
            console.warn(`[loadCoordinateValues] Error loading obsm coordinate:`, e);
            return new Array(nCells).fill(0);
        }
    }
    return new Array(nCells).fill(0);
}

/**
 * Get expression values for a single gene across all cells.
 * Uses the sparse CSC (Compressed Sparse Column) matrix format.
 * CSC stores data by columns (genes), so we can efficiently load just the data for one gene.
 * 
 * @param {string} geneName - Name of the gene to look up
 * @returns {Float32Array} - Expression values for each cell (0 for cells with no expression)
 */
async function getGeneExpression(geneName) {
    if (!sparseMatrix.geneNames || !zarrRoot) {
        console.error('[getGeneExpression] Sparse matrix or zarr root not loaded');
        return null;
    }
    
    // Find gene index
    const geneIdx = sparseMatrix.geneNames.indexOf(geneName);
    if (geneIdx === -1) {
        console.warn(`[getGeneExpression] Gene "${geneName}" not found`);
        return null;
    }
    
    const nCells = sparseMatrix.shape[0];
    const result = new Float32Array(nCells); // Initialize with zeros
    
    const t0 = performance.now();
    
    // Initialize cached zarr arrays on first call (just the array handles, not all data)
    if (!cachedZarrArrays) {
        console.log('[getGeneExpression] Initializing sparse matrix arrays...');
        
        const indptrArr = await zarr.open(zarrRoot.resolve('X/indptr'), { kind: 'array' });
        const indicesArr = await zarr.open(zarrRoot.resolve('X/indices'), { kind: 'array' });
        const dataArr = await zarr.open(zarrRoot.resolve('X/data'), { kind: 'array' });
        
        // Load full indptr (small - one value per gene + 1)
        const indptr = await zarr.get(indptrArr);
        
        cachedZarrArrays = {
            indptr: indptr.data,
            indicesArr,
            dataArr
        };
        
        console.log(`[getGeneExpression] indptr loaded: ${cachedZarrArrays.indptr.length} entries`);
    }
    
    // For CSC format: get the slice range for this gene from indptr
    const start = cachedZarrArrays.indptr[geneIdx];
    const end = cachedZarrArrays.indptr[geneIdx + 1];
    
    if (end > start) {
        // Only load the needed slice of indices and data for this gene
        const geneIndices = await zarr.get(cachedZarrArrays.indicesArr, [zarr.slice(start, end)]);
        const geneData = await zarr.get(cachedZarrArrays.dataArr, [zarr.slice(start, end)]);
        
        // Build the dense expression array for this gene
        for (let i = 0; i < geneIndices.data.length; i++) {
            const cellIdx = geneIndices.data[i];
            result[cellIdx] = geneData.data[i];
        }
        
        console.log(`[getGeneExpression] Gene ${geneName}: loaded ${geneIndices.data.length} non-zero values in ${(performance.now() - t0).toFixed(0)}ms`);
    } else {
        console.log(`[getGeneExpression] Gene ${geneName}: no expression (all zeros)`);
    }
    
    return result;
}

// Load data from zarr store
async function loadData() {
    const loadingEl = document.getElementById('loading');
    let loadingText = loadingEl.querySelector('.loading-text');
    
    // If loading-text doesn't exist, create the structure
    if (!loadingText) {
        loadingEl.innerHTML = '<div class="loading-spinner"></div><div class="loading-text">Loading data... This may take a moment.</div>';
        loadingText = loadingEl.querySelector('.loading-text');
    }
    
    // Ensure loading is visible
    loadingEl.style.display = 'flex';
    loadingText.textContent = 'Loading zarr data...';
    
    try {
        const loadStartTime = Date.now();
        
        // Open zarr store - use full URL
        console.log(`[loadData] Opening zarr store: ${ZARR_PATH}`);
        const baseUrl = new URL(ZARR_PATH, window.location.href).href;
        zarrBaseUrl = baseUrl; // Save for lazy loading
        const store = new zarr.FetchStore(baseUrl);
        const root = zarr.root(store);
        zarrRoot = root; // Save for loading genes later
        
        // Load obs group to discover columns
        loadingText.textContent = 'Reading observation metadata...';
        
        // Get the obs index (cell barcodes) - try different possible locations
        let cellBarcodes;
        try {
            const indexData = await loadZarrArray(root, 'obs/_index');
            cellBarcodes = Array.from(indexData.data);
        } catch (e) {
            console.warn('[loadData] Could not load obs/_index, trying obs/barcode');
            const barcodeData = await loadZarrArray(root, 'obs/barcode');
            cellBarcodes = Array.from(barcodeData.data);
        }
        
        const nCells = cellBarcodes.length;
        console.log(`[loadData] Found ${nCells} cells`);
        
        // Initialize data array
        allData = new Array(nCells);
        for (let i = 0; i < nCells; i++) {
            allData[i] = { barcode: cellBarcodes[i] };
        }
        
        // Discover obs columns metadata (but don't load data - lazy load on demand)
        loadingText.textContent = 'Discovering column metadata...';
        const attrsResponse = await fetch(`${baseUrl}/obs/.zattrs`);
        const obsAttrs = await attrsResponse.json();
        const columnOrder = obsAttrs['column-order'] || [];
        
        console.log(`[loadData] Found ${columnOrder.length} obs columns (metadata only, data will be loaded on demand)`);
        
        // Determine column types from metadata (don't load actual data)
        const numericColumns = new Set(['global_x', 'global_y', 'global_z']);
        
        // Initialize metadata tracking
        columnMetadata = {};
        column_names_categorical = [];
        column_names_continuous = [];
        loadedColumns.clear();
        
        for (const colName of columnOrder) {
            try {
                // Check the column's encoding type from .zattrs
                let encodingType = null;
                try {
                    const colAttrsResponse = await fetch(`${baseUrl}/obs/${colName}/.zattrs`);
                    if (colAttrsResponse.ok) {
                        const colAttrs = await colAttrsResponse.json();
                        encodingType = colAttrs['encoding-type'];
                    }
                } catch (e) {
                    // Ignore - will default to array
                }
                
                // Determine if it's numeric based on encoding type or known numeric columns
                const isNumeric = encodingType === 'array' || numericColumns.has(colName);
                
                // Store metadata
                columnMetadata[colName] = {
                    type: isNumeric ? 'continuous' : 'categorical',
                    encodingType: encodingType || 'array',
                    path: colName
                };
                
                // Track column names by type (for UI)
                if (isNumeric) {
                    if (!column_names_continuous.includes(colName)) {
                        column_names_continuous.push(colName);
                    }
                    // Initialize range (will be computed when loaded)
                    continuousRanges[colName] = { min: Infinity, max: -Infinity };
                } else {
                    if (!column_names_categorical.includes(colName)) {
                        column_names_categorical.push(colName);
                    }
                    // Initialize attribute values set (will be populated when loaded)
                    attributeValues[colName] = new Set();
                }
            } catch (colError) {
                console.warn(`[loadData] Could not get metadata for column ${colName}:`, colError);
            }
        }
        
        console.log(`[loadData] Discovered ${column_names_categorical.length} categorical and ${column_names_continuous.length} continuous columns`);
        
        // Discover available coordinate sources
        loadingText.textContent = 'Discovering coordinate sources...';
        availableCoordinateSources = await discoverCoordinateSources(root, baseUrl);
        
        // Set default coordinate selections (only from obsm embeddings)
        if (!selectedXCoord || !selectedYCoord) {
            // Try to find global_x and global_y first (from obsm Global_Spatial)
            let globalX = availableCoordinateSources.obsm.find(c => 
                c.embedding === 'Global_Spatial' && c.columnName === 'global_x');
            let globalY = availableCoordinateSources.obsm.find(c => 
                c.embedding === 'Global_Spatial' && c.columnName === 'global_y');
            
            if (globalX && globalY) {
                selectedXCoord = globalX;
                selectedYCoord = globalY;
            } else {
                // Try to find spatial coordinates
                const spatialX = availableCoordinateSources.obsm.find(c => 
                    c.embedding === 'spatial' && (c.columnName === 'x' || c.columnIndex === 0));
                const spatialY = availableCoordinateSources.obsm.find(c => 
                    c.embedding === 'spatial' && (c.columnName === 'y' || c.columnIndex === 1));
                
                if (spatialX && spatialY) {
                    selectedXCoord = spatialX;
                    selectedYCoord = spatialY;
                } else {
                    // Use first two available obsm dimensions
                    if (availableCoordinateSources.obsm.length >= 2) {
                        selectedXCoord = availableCoordinateSources.obsm[0];
                        selectedYCoord = availableCoordinateSources.obsm[1];
                    } else {
                        console.error('[loadData] No obsm coordinate sources found');
                        throw new Error('No obsm coordinate sources found. Please check the zarr file structure.');
                    }
                }
            }
        }
        
        // Z coordinate defaults to None (null)
        if (!selectedZCoord) {
            selectedZCoord = null;
        }
        
        console.log('[loadData] Selected coordinates:', {
            x: selectedXCoord?.displayName,
            y: selectedYCoord?.displayName,
            z: selectedZCoord ? selectedZCoord.displayName : 'None'
        });
        
        // Load coordinate values
        loadingText.textContent = 'Loading coordinates...';
        const xValues = await loadCoordinateValues(root, selectedXCoord, nCells);
        const yValues = await loadCoordinateValues(root, selectedYCoord, nCells);
        
        // Load z coordinate if selected (optional, can be None)
        let zValues = null;
        if (selectedZCoord) {
            zValues = await loadCoordinateValues(root, selectedZCoord, nCells);
        }
        
        // Map coordinate columns to x, y, z
        for (let i = 0; i < nCells; i++) {
            allData[i].x = xValues[i] || 0;
            allData[i].y = yValues[i] || 0;
            allData[i].z = zValues ? (zValues[i] || 0) : 0;
        }
        
        // Update coordinate selection UI
        updateCoordinateSelectionUI();
        
        // Load sparse matrix metadata for gene lookups
        // We don't load the full data here - just the shape and gene names
        // The actual sparse data is loaded on-demand when genes are requested
        loadingText.textContent = 'Loading gene information...';
        
        try {
            // Get shape from X/.zattrs
            const xAttrsResponse = await fetch(`${baseUrl}/X/.zattrs`);
            const xAttrs = await xAttrsResponse.json();
            sparseMatrix.shape = xAttrs.shape;
            
            console.log(`[loadData] Sparse matrix shape: ${sparseMatrix.shape[0]} x ${sparseMatrix.shape[1]}`);
            
            // Load gene names from var index
            try {
                const varIndexData = await loadZarrArray(root, 'var/_index');
                sparseMatrix.geneNames = Array.from(varIndexData.data);
                console.log(`[loadData] Loaded ${sparseMatrix.geneNames.length} gene names`);
                console.log(`[loadData] First 10 genes:`, sparseMatrix.geneNames.slice(0, 10));
            } catch (varError) {
                console.warn('[loadData] Could not load gene names:', varError);
                sparseMatrix.geneNames = [];
            }
            
            // Discover var column metadata (but don't load data - lazy load when Genes tab is opened)
            loadingText.textContent = 'Discovering var column metadata...';
            try {
                // Get var column order from .zattrs
                const varAttrsResponse = await fetch(`${baseUrl}/var/.zattrs`);
                const varAttrs = await varAttrsResponse.json();
                const varColumnOrder = varAttrs['column-order'] || [];
                
                console.log(`[loadData] Found ${varColumnOrder.length} var columns (metadata only, data will be loaded on demand)`);
                
                // Initialize metadata tracking
                varColumnMetadata = {};
                
                for (const colName of varColumnOrder) {
                    try {
                        // Check encoding type from .zattrs
                        let encodingType = null;
                        try {
                            const colAttrsResponse = await fetch(`${baseUrl}/var/${colName}/.zattrs`);
                            if (colAttrsResponse.ok) {
                                const colAttrs = await colAttrsResponse.json();
                                encodingType = colAttrs['encoding-type'];
                            }
                        } catch (e) {
                            // Not categorical, or can't determine - default to array
                        }
                        
                        // Store metadata
                        varColumnMetadata[colName] = {
                            encodingType: encodingType || 'array',
                            path: colName
                        };
                    } catch (colError) {
                        console.warn(`[loadData] Could not get metadata for var column ${colName}:`, colError);
                    }
                }
                
                // Initialize geneStats with just gene names (columns will be loaded later)
                geneStats = sparseMatrix.geneNames.map(name => ({ gene: name }));
                
                console.log(`[loadData] Discovered ${Object.keys(varColumnMetadata).length} var columns (not loaded)`);
            } catch (statsError) {
                console.warn('[loadData] Could not discover var column metadata:', statsError);
                geneStats = sparseMatrix.geneNames.map(name => ({ gene: name }));
            }
        } catch (sparseError) {
            console.warn('[loadData] Could not load sparse matrix info:', sparseError);
        }
        
        const loadTime = ((Date.now() - loadStartTime) / 1000).toFixed(1);
        console.log(`[loadData] Loaded zarr in ${loadTime}s. Total cells: ${allData.length}`);
        
        // Log first few points for debugging
        for (let i = 0; i < Math.min(5, allData.length); i++) {
            const p = allData[i];
            console.log(`Sample point ${i + 1}: x=${p.x?.toFixed(2)}, y=${p.y?.toFixed(2)}, z=${p.z?.toFixed(2)}`);
        }
        
        loadingText.textContent = `Loaded ${allData.length.toLocaleString()} cells. Initializing visualization...`;
        document.getElementById('pointCount').textContent = `Total cells: ${allData.length.toLocaleString()}`;
        await new Promise(resolve => setTimeout(resolve, 100));
        
        // Calculate and log coordinate ranges
        if (allData.length > 0) {
            let xMin = Infinity, xMax = -Infinity;
            let yMin = Infinity, yMax = -Infinity;
            let zMin = Infinity, zMax = -Infinity;
            
            for (let i = 0; i < Math.min(10000, allData.length); i++) {
                const p = allData[i];
                if (p.x !== undefined) { xMin = Math.min(xMin, p.x); xMax = Math.max(xMax, p.x); }
                if (p.y !== undefined) { yMin = Math.min(yMin, p.y); yMax = Math.max(yMax, p.y); }
                if (p.z !== undefined) { zMin = Math.min(zMin, p.z); zMax = Math.max(zMax, p.z); }
            }
            
            console.log(`Coordinate ranges:`);
            console.log(`  x: [${xMin.toFixed(2)}, ${xMax.toFixed(2)}]`);
            console.log(`  y: [${yMin.toFixed(2)}, ${yMax.toFixed(2)}]`);
            console.log(`  z: [${zMin.toFixed(2)}, ${zMax.toFixed(2)}]`);
        }
        
        // Initialize visible indices
        visibleIndices = new Uint32Array(allData.length);
        for (let i = 0; i < allData.length; i++) {
            visibleIndices[i] = i;
        }
        
        // Populate colorBy dropdown with "Gene" option first, then obs columns
        const colorBySelect = document.getElementById('colorBy');
        colorBySelect.innerHTML = '';
        
        // Add "Gene" option first
        const geneOption = document.createElement('option');
        geneOption.value = 'Gene';
        geneOption.textContent = 'Gene';
        colorBySelect.appendChild(geneOption);
        
        const obsAttributes = [...column_names_categorical, ...column_names_continuous];
        obsAttributes.forEach(attr => {
            const option = document.createElement('option');
            option.value = attr;
            option.textContent = attr;
            colorBySelect.appendChild(option);
        });
        
        // Set first obs attribute as default (not "Gene" unless a gene is selected)
        if (obsAttributes.length > 0) {
            colorBySelect.value = obsAttributes[0];
        }
        
        // Setup gene autocomplete
        setupGeneAutocomplete(sparseMatrix.geneNames || [])
        
        // Build filter UI
        renderFilters();
        
        // Create initial visualization
        loadingText.textContent = 'Rendering visualization...';
        await createPointCloud();
        
        // Initialize legend
        updateLegend();
        
        // Set up event listeners
        setupEventListeners();
        
        // Start animation loop
        animate();
        
        // Hide loading message
        setTimeout(() => {
            loadingEl.style.display = 'none';
        }, 500);
        
    } catch (error) {
        console.error('Error loading data:', error);
        loadingText.textContent = 'Error loading data. Please check the console.';
        loadingEl.style.background = 'rgba(231, 76, 60, 0.9)';
        loadingEl.style.borderColor = 'rgba(192, 57, 43, 0.5)';
    }
}

// Setup gene autocomplete functionality
function setupGeneAutocomplete(geneNames) {
    const geneInput = document.getElementById('geneInput');
    const geneSuggestions = document.getElementById('geneSuggestions');
    const clearGeneBtn = document.getElementById('clearGene');
    
    if (!geneInput || !geneSuggestions) {
        console.warn('[setupGeneAutocomplete] Gene input elements not found');
        return;
    }
    
    let selectedIndex = -1;
    let currentSuggestions = [];
    
    // Filter and show suggestions
    function showSuggestions(query) {
        if (!query || query.length < 1) {
            geneSuggestions.style.display = 'none';
            return;
        }
        
        const queryLower = query.toLowerCase();
        // Find matches - prioritize starts-with, then contains
        const startsWithMatches = geneNames.filter(g => g.toLowerCase().startsWith(queryLower));
        const containsMatches = geneNames.filter(g => 
            !g.toLowerCase().startsWith(queryLower) && g.toLowerCase().includes(queryLower)
        );
        
        currentSuggestions = [...startsWithMatches, ...containsMatches].slice(0, 20);
        
        if (currentSuggestions.length === 0) {
            geneSuggestions.innerHTML = '<div class="gene-suggestion" style="color: #888;">No matching genes</div>';
            geneSuggestions.style.display = 'block';
            return;
        }
        
        geneSuggestions.innerHTML = currentSuggestions.map((gene, idx) => 
            `<div class="gene-suggestion${idx === selectedIndex ? ' selected' : ''}" data-gene="${gene}">${gene}</div>`
        ).join('');
        geneSuggestions.style.display = 'block';
        selectedIndex = -1;
    }
    
    // Select a gene
    async function selectGene(geneName) {
        if (!geneName || !geneNames.includes(geneName)) {
            return;
        }
        
        selectedGene = geneName;
        geneInput.value = geneName;
        geneInput.classList.add('has-gene');
        geneSuggestions.style.display = 'none';
        clearGeneBtn.style.display = 'inline-block';
        
        // Automatically set Color By to "Gene" when a gene is selected
        const colorBySelect = document.getElementById('colorBy');
        if (colorBySelect) {
            colorBySelect.value = 'Gene';
        }
        
        console.log(`[Gene] Selected gene: ${geneName}, Color By set to Gene`);
        
        // Trigger re-render with gene coloring
        await createPointCloud();
        
        // Update legend (which will add winsorization controls)
        updateLegend();
    }
    
    // Expose selectGene globally for gene table
    selectGeneGlobal = selectGene;
    
    // Clear gene selection
    async function clearGene() {
        selectedGene = null;
        geneInput.value = '';
        geneInput.classList.remove('has-gene');
        geneSuggestions.style.display = 'none';
        clearGeneBtn.style.display = 'none';
        geneExpressionCache = { geneName: null, data: null, min: 0, max: 1, winsorizedMin: 0, winsorizedMax: 1 };
        
        // Hide winsorization controls when gene is cleared
        const winsorizationGroup = document.getElementById('geneWinsorizationGroup');
        if (winsorizationGroup) {
            winsorizationGroup.style.display = 'none';
        }
        
        // If Color By is set to "Gene", change it to first available obs attribute
        const colorBySelect = document.getElementById('colorBy');
        if (colorBySelect && colorBySelect.value === 'Gene') {
            const obsAttributes = [...column_names_categorical, ...column_names_continuous];
            if (obsAttributes.length > 0) {
                colorBySelect.value = obsAttributes[0];
            }
        }
        
        console.log('[Gene] Cleared gene selection');
        
        // Trigger re-render with obs coloring
        await createPointCloud();
    }
    
    // Input event handler
    geneInput.addEventListener('input', (e) => {
        showSuggestions(e.target.value);
    });
    
    // Focus event - show suggestions if there's text
    geneInput.addEventListener('focus', () => {
        if (geneInput.value) {
            showSuggestions(geneInput.value);
        }
    });
    
    // Keyboard navigation
    geneInput.addEventListener('keydown', async (e) => {
        if (geneSuggestions.style.display !== 'block' || currentSuggestions.length === 0) {
            return;
        }
        
        if (e.key === 'ArrowDown') {
            e.preventDefault();
            selectedIndex = Math.min(selectedIndex + 1, currentSuggestions.length - 1);
            updateSelectedSuggestion();
        } else if (e.key === 'ArrowUp') {
            e.preventDefault();
            selectedIndex = Math.max(selectedIndex - 1, 0);
            updateSelectedSuggestion();
        } else if (e.key === 'Enter') {
            e.preventDefault();
            if (selectedIndex >= 0 && selectedIndex < currentSuggestions.length) {
                await selectGene(currentSuggestions[selectedIndex]);
            } else if (currentSuggestions.length > 0) {
                await selectGene(currentSuggestions[0]);
            }
        } else if (e.key === 'Escape') {
            geneSuggestions.style.display = 'none';
        }
    });
    
    function updateSelectedSuggestion() {
        const items = geneSuggestions.querySelectorAll('.gene-suggestion[data-gene]');
        items.forEach((item, idx) => {
            item.classList.toggle('selected', idx === selectedIndex);
        });
        
        // Scroll into view
        if (selectedIndex >= 0 && items[selectedIndex]) {
            items[selectedIndex].scrollIntoView({ block: 'nearest' });
        }
    }
    
    // Click on suggestion
    geneSuggestions.addEventListener('click', async (e) => {
        const suggestion = e.target.closest('.gene-suggestion[data-gene]');
        if (suggestion) {
            await selectGene(suggestion.dataset.gene);
        }
    });
    
    // Clear button
    clearGeneBtn.addEventListener('click', clearGene);
    
    // Hide suggestions when clicking outside
    document.addEventListener('click', (e) => {
        if (!geneInput.contains(e.target) && !geneSuggestions.contains(e.target)) {
            geneSuggestions.style.display = 'none';
        }
    });
    
    console.log(`[setupGeneAutocomplete] Initialized with ${geneNames.length} genes`);
}

// Change color for a specific entity
function changeEntityColor(attribute, value, colorKey, colorDivElement) {
    // Get current color
    const currentColor = colorMap.get(colorKey) || getColorForValue(value, attribute);
    const currentHex = '#' + 
        Math.round(currentColor.r * 255).toString(16).padStart(2, '0') +
        Math.round(currentColor.g * 255).toString(16).padStart(2, '0') +
        Math.round(currentColor.b * 255).toString(16).padStart(2, '0');
    
    // Create a color input
    const colorInput = document.createElement('input');
    colorInput.type = 'color';
    colorInput.value = currentHex;
    colorInput.style.position = 'absolute';
    colorInput.style.opacity = '0';
    colorInput.style.width = '0';
    colorInput.style.height = '0';
    colorInput.style.pointerEvents = 'none';
    
    // Add to body temporarily
    document.body.appendChild(colorInput);
    
    // Trigger color picker
    colorInput.click();
    
    // Listen for change
    colorInput.addEventListener('change', async (event) => {
        const newHex = event.target.value;
        
        // Parse hex color to THREE.Color
        const r = parseInt(newHex.slice(1, 3), 16) / 255;
        const g = parseInt(newHex.slice(3, 5), 16) / 255;
        const b = parseInt(newHex.slice(5, 7), 16) / 255;
        
        const newColor = new THREE.Color(r, g, b);
        
        // Update color map
        colorMap.set(colorKey, newColor);
        
        // Update the color div in legend
        colorDivElement.style.backgroundColor = newHex;
        
        // Re-render the point cloud with new colors
        if (pointCloud) {
            await createPointCloud();
        }
        
        // Clean up
        document.body.removeChild(colorInput);
        
        console.log(`[Color Change] Changed color for ${attribute}:${value} to ${newHex}`);
    });
    
    // Also handle if user cancels (click outside)
    colorInput.addEventListener('blur', () => {
        setTimeout(() => {
            if (document.body.contains(colorInput)) {
                document.body.removeChild(colorInput);
            }
        }, 100);
    });
}

// Cache for gene expression data
let geneExpressionCache = {
    geneName: null,
    data: null,
    min: 0,           // Actual min value
    max: 1,           // Actual max value
    winsorizedMin: 0, // Winsorized min (for color scale)
    winsorizedMax: 1  // Winsorized max (for color scale)
};

// Generate color for a value
function getColorForValue(value, attribute) {
    if (value === null || value === undefined || value === '') return new THREE.Color(0x888888);
    
    // Handle gene expression (attribute starts with "gene:")
    if (attribute.startsWith('gene:')) {
        if (typeof value === 'number') {
            const range = geneExpressionCache;
            const winMin = range.winsorizedMin !== undefined ? range.winsorizedMin : range.min;
            const winMax = range.winsorizedMax !== undefined ? range.winsorizedMax : range.max;
            
            if (winMax > winMin) {
                // Winsorize the value (clip to min/max range)
                const winsorizedValue = Math.max(winMin, Math.min(winMax, value));
                // Normalize to 0-1 range
                const normalized = (winsorizedValue - winMin) / (winMax - winMin);
                
                // Use blue-white-red divergent color palette
                // Blue (low) -> White (middle) -> Red (high)
                let r, g, b;
                if (normalized < 0.5) {
                    // Blue to white: normalized goes from 0 to 0.5
                    const t = normalized * 2; // Scale to 0-1
                    r = t;
                    g = t;
                    b = 1.0; // Full blue at bottom
                } else {
                    // White to red: normalized goes from 0.5 to 1
                    const t = (normalized - 0.5) * 2; // Scale to 0-1
                    r = 1.0; // Full red at top
                    g = 1.0 - t;
                    b = 1.0 - t;
                }
                
                return new THREE.Color(r, g, b);
            }
        }
        // Zero or below min expression - use blue
        return new THREE.Color(0, 0, 1); // Blue
    }
    
    // For continuous variables, use a gradient based on the value
    if (column_names_continuous.includes(attribute) && typeof value === 'number') {
        const range = continuousRanges[attribute];
        if (range && range.max > range.min) {
            const normalized = (value - range.min) / (range.max - range.min);
            const color = new THREE.Color();
            // Use a color gradient from blue to red
            color.setHSL((1 - normalized) * 0.7, 0.8, 0.5);
            return color;
        }
    }
    
    const key = `${attribute}:${value}`;
    
    if (!colorMap.has(key)) {
        // Generate a color based on hash of the value
        const strValue = String(value);
        let hash = 0;
        for (let i = 0; i < strValue.length; i++) {
            hash = strValue.charCodeAt(i) + ((hash << 5) - hash);
        }
        
        const hue = (hash % 360 + 360) % 360;
        const saturation = 70 + (hash % 20);
        const lightness = 50 + (hash % 20);
        
        const color = new THREE.Color();
        color.setHSL(hue / 360, saturation / 100, lightness / 100);
        colorMap.set(key, color);
    }
    
    return colorMap.get(key);
}

// Randomize colors for a categorical variable using rainbow palette
async function randomizeCategoricalColors(attribute, values) {
    if (!values || values.length === 0) return;
    
    console.log(`[randomizeCategoricalColors] Randomizing colors for ${values.length} values in ${attribute}`);
    
    // Generate a rainbow palette - evenly spaced hues across the spectrum
    const nValues = values.length;
    const rainbowColors = [];
    
    for (let i = 0; i < nValues; i++) {
        // Distribute hues evenly across 0-360 degrees
        const hue = (i / nValues) * 360;
        // Use high saturation and medium lightness for vibrant colors
        const saturation = 0.8 + (Math.random() * 0.2); // 80-100% saturation
        const lightness = 0.5 + (Math.random() * 0.1); // 50-60% lightness
        
        const color = new THREE.Color();
        color.setHSL(hue / 360, saturation, lightness);
        rainbowColors.push(color);
    }
    
    // Shuffle the colors randomly
    for (let i = rainbowColors.length - 1; i > 0; i--) {
        const j = Math.floor(Math.random() * (i + 1));
        [rainbowColors[i], rainbowColors[j]] = [rainbowColors[j], rainbowColors[i]];
    }
    
    // Assign shuffled colors to values
    values.forEach((value, index) => {
        const colorKey = `${attribute}:${value}`;
        colorMap.set(colorKey, rainbowColors[index]);
    });
    
    // Recreate point cloud with new colors
    if (pointCloud) {
        await createPointCloud();
    }
    
    // Update legend to show new colors
    updateLegend();
    
    console.log(`[randomizeCategoricalColors] Colors randomized for ${nValues} values`);
}

// Update the color legend
async function updateLegend() {
    const legendDiv = document.getElementById('legend');
    if (!legendDiv) return;
    
    const colorByDropdown = document.getElementById('colorBy').value;
    
    // Determine what we're coloring by: check if Color By is set to "Gene"
    const isGene = colorByDropdown === 'Gene' && selectedGene !== null;
    const colorBy = isGene ? `gene:${selectedGene}` : colorByDropdown;
    
    // Ensure the column is loaded if it's not a gene
    if (!isGene && colorByDropdown && colorByDropdown !== 'Gene') {
        await ensureColumnLoaded(colorByDropdown);
    }
    
    // Get unique values from visible data
    const visibleValues = new Set();
    const isContinuous = column_names_continuous.includes(colorByDropdown) || isGene;
    
    if (visibleIndices && visibleIndices.length > 0) {
        for (let i = 0; i < visibleIndices.length; i++) {
            const idx = visibleIndices[i];
            const point = allData[idx];
            
            if (isGene && geneExpressionCache.data) {
                // Use cached gene expression data
                const val = geneExpressionCache.data[idx];
                if (val !== null && val !== undefined) {
                    visibleValues.add(val);
                }
            } else if (isContinuous) {
                if (point[colorByDropdown] !== null && point[colorByDropdown] !== undefined) {
                    visibleValues.add(point[colorByDropdown]);
                }
            } else {
                const value = point[colorByDropdown] || '';
                if (value) {
                    visibleValues.add(value);
                }
            }
        }
    }
    
    legendDiv.innerHTML = '';
    
    if (isContinuous) {
        // Show gradient for continuous values
        if (visibleValues.size > 0) {
            const continuousValues = Array.from(visibleValues).map(v => parseFloat(v)).filter(v => !isNaN(v));
            if (continuousValues.length > 0) {
                // Use reduce to avoid stack overflow with large arrays
                const minVal = continuousValues.reduce((min, val) => val < min ? val : min, continuousValues[0]);
                const maxVal = continuousValues.reduce((max, val) => val > max ? val : max, continuousValues[0]);
                
                // Create gradient canvas
                const canvas = document.createElement('canvas');
                canvas.width = 200;
                canvas.height = 30;
                canvas.className = 'legend-gradient';
                const ctx = canvas.getContext('2d');
                
                const gradient = ctx.createLinearGradient(0, 0, canvas.width, 0);
                
                // For gene expression, use winsorized range if available
                let displayMin = minVal;
                let displayMax = maxVal;
                if (isGene && geneExpressionCache.winsorizedMin !== undefined && geneExpressionCache.winsorizedMax !== undefined) {
                    displayMin = geneExpressionCache.winsorizedMin;
                    displayMax = geneExpressionCache.winsorizedMax;
                }
                
                for (let i = 0; i <= 100; i++) {
                    const normalized = i / 100;
                    const value = displayMin + (displayMax - displayMin) * normalized;
                    const color = getColorForValue(value, colorBy);
                    const stop = i / 100;
                    gradient.addColorStop(stop, `rgb(${Math.round(color.r * 255)}, ${Math.round(color.g * 255)}, ${Math.round(color.b * 255)})`);
                }
                
                ctx.fillStyle = gradient;
                ctx.fillRect(0, 0, canvas.width, canvas.height);
                legendDiv.appendChild(canvas);
                
                // For non-gene continuous variables, show min/max labels
                if (!isGene) {
                    const labelsDiv = document.createElement('div');
                    labelsDiv.className = 'legend-gradient-labels';
                    labelsDiv.innerHTML = `<span>${minVal.toFixed(4)}</span><span>${maxVal.toFixed(4)}</span>`;
                    legendDiv.appendChild(labelsDiv);
                }
                
                // For gene expression, add winsorization controls inside legend
                if (isGene && geneExpressionCache.winsorizedMin !== undefined && geneExpressionCache.winsorizedMax !== undefined) {
                    addGeneWinsorizationControlsToLegend(legendDiv, colorBy);
                }
            } else {
                legendDiv.innerHTML = `<div class="legend-label">No ${isGene ? selectedGene : colorByDropdown} data</div>`;
            }
        } else {
            legendDiv.innerHTML = '<div class="legend-label">No visible data</div>';
        }
    } else {
        // Show categorical legend
        const sortedValues = Array.from(visibleValues).sort();
        
        if (sortedValues.length === 0) {
            legendDiv.innerHTML = '<div class="legend-label">No visible data</div>';
            return;
        }
        
        // Add "Randomize Colors" button for categorical variables
        const randomizeButton = document.createElement('button');
        randomizeButton.textContent = 'Randomize Colors';
        randomizeButton.style.cssText = `
            margin-top: 0px;
            margin-bottom: 12px;
            padding: 6px 12px;
            background: rgba(255, 255, 255, 0.1);
            border: 1px solid rgba(255, 255, 255, 0.2);
            border-radius: 4px;
            color: white;
            cursor: pointer;
            font-size: 0.9em;
            transition: background 0.2s;
        `;
        randomizeButton.addEventListener('mouseenter', () => {
            randomizeButton.style.background = 'rgba(255, 255, 255, 0.2)';
        });
        randomizeButton.addEventListener('mouseleave', () => {
            randomizeButton.style.background = 'rgba(255, 255, 255, 0.1)';
        });
        randomizeButton.addEventListener('click', async () => {
            await randomizeCategoricalColors(colorBy, sortedValues);
        });
        legendDiv.appendChild(randomizeButton);
        
        // Limit to first 100 items for performance
        const displayValues = sortedValues.slice(0, 100);
        const remainingCount = sortedValues.length - displayValues.length;
        
        displayValues.forEach(value => {
            const itemDiv = document.createElement('div');
            itemDiv.className = 'legend-item';
            itemDiv.style.cursor = 'pointer';
            itemDiv.title = 'Click to change color';
            
            const colorDiv = document.createElement('div');
            colorDiv.className = 'legend-color';
            const color = getColorForValue(value, colorBy);
            const colorKey = `${colorBy}:${value}`;
            colorDiv.style.backgroundColor = `rgb(${Math.round(color.r * 255)}, ${Math.round(color.g * 255)}, ${Math.round(color.b * 255)})`;
            
            const labelDiv = document.createElement('div');
            labelDiv.className = 'legend-label';
            labelDiv.textContent = value || '(empty)';
            
            // Add click handler to change color
            itemDiv.addEventListener('click', (event) => {
                event.stopPropagation();
                changeEntityColor(colorBy, value, colorKey, colorDiv);
            });
            
            // Add hover effect
            itemDiv.addEventListener('mouseenter', () => {
                itemDiv.style.backgroundColor = 'rgba(255, 255, 255, 0.1)';
                itemDiv.style.borderRadius = '4px';
            });
            
            itemDiv.addEventListener('mouseleave', () => {
                itemDiv.style.backgroundColor = 'transparent';
            });
            
            itemDiv.appendChild(colorDiv);
            itemDiv.appendChild(labelDiv);
            legendDiv.appendChild(itemDiv);
        });
        
        if (remainingCount > 0) {
            const moreDiv = document.createElement('div');
            moreDiv.className = 'legend-label';
            moreDiv.style.fontStyle = 'italic';
            moreDiv.style.color = '#95a5a6';
            moreDiv.textContent = `... and ${remainingCount} more`;
            legendDiv.appendChild(moreDiv);
        }
    }
}

// Set camera to x-y plane view
function setCameraToXYPlaneView(geometry) {
    geometry.computeBoundingBox();
    const box = geometry.boundingBox;
    const center = new THREE.Vector3();
    box.getCenter(center);
    const size = box.getSize(new THREE.Vector3());
    
    // Calculate the extent in x-y plane
    const xyExtent = Math.max(size.x, size.y);
    
    // Position camera above the center (along z-axis), looking down at x-y plane
    // Calculate distance needed to see the full x-y extent
    const fovRad = camera.fov * (Math.PI / 180);
    
    // Calculate distance needed to fit the larger of x or y extent
    // For perspective camera: height_visible = 2 * distance * tan(fov/2)
    const halfHeight = xyExtent / 2;
    const distance = halfHeight / Math.tan(fovRad / 2);
    
    // Add some padding (10% margin)
    const cameraHeight = Math.max(distance * 1.1, size.z * 1.5, 100);
    
    const cameraPosition = new THREE.Vector3(
        center.x,
        center.y,
        center.z + cameraHeight
    );
    
    camera.position.copy(cameraPosition);
    camera.lookAt(center);
    controls.target.copy(center);
    controls.update();
    
    // Store initial state for reset
    initialCameraState.position = cameraPosition.clone();
    initialCameraState.target = center.clone();
    
    return { position: cameraPosition.clone(), target: center.clone() };
}

// Create point cloud with spheres
async function createPointCloud() {
    // Remove existing point cloud/spheres
    if (pointCloud) {
        scene.remove(pointCloud);
        pointCloud.geometry.dispose();
        pointCloud.material.dispose();
    }
    if (sphereMesh) {
        scene.remove(sphereMesh);
        sphereMesh.geometry.dispose();
        sphereMesh.material.dispose();
    }
    
    // Hide highlight when recreating point cloud
    if (highlightSphere) {
        highlightSphere.visible = false;
    }
    
    if (!visibleIndices || visibleIndices.length === 0) {
        document.getElementById('visibleCount').textContent = 'Visible points: 0';
        return;
    }
    
    const colorBy = document.getElementById('colorBy').value;
    const pointSize = parseFloat(document.getElementById('pointSize').value);
    const sampleRate = Math.max(0.01, Math.min(1, parseInt(document.getElementById('sampleRate').value) / 100));
    
    // Determine what to color by: check if Color By is set to "Gene"
    const colorByGene = colorBy === 'Gene' && selectedGene !== null;
    const effectiveColorBy = colorByGene ? `gene:${selectedGene}` : colorBy;
    
    // Ensure the column is loaded if it's not a gene
    if (!colorByGene && colorBy && colorBy !== 'Gene') {
        await ensureColumnLoaded(colorBy);
    }
    
    // Handle gene expression coloring
    let geneExpression = null;
    if (colorByGene) {
        const geneName = selectedGene;
        
        // Load gene expression if not cached or different gene
        if (geneExpressionCache.geneName !== geneName) {
            console.log(`[createPointCloud] Loading gene expression for: ${geneName}`);
            geneExpression = await getGeneExpression(geneName);
            
            if (geneExpression) {
                // Calculate min/max for normalization
                let min = Infinity, max = -Infinity;
                for (let i = 0; i < geneExpression.length; i++) {
                    const val = geneExpression[i];
                    if (val > 0) { // Only consider non-zero for range
                        min = Math.min(min, val);
                        max = Math.max(max, val);
                    }
                }
                if (min === Infinity) min = 0;
                if (max === -Infinity) max = 1;
                
                // Initialize winsorized range to actual range
                geneExpressionCache = {
                    geneName: geneName,
                    data: geneExpression,
                    min: 0, // Use 0 as min for better visualization
                    max: max,
                    winsorizedMin: 0,
                    winsorizedMax: max
                };
                console.log(`[createPointCloud] Gene ${geneName} range: [0, ${max.toFixed(4)}]`);
                
                // Update winsorization controls with actual range
                updateGeneWinsorizationControls();
            } else {
                console.warn(`[createPointCloud] Could not load gene: ${geneName}`);
            }
        } else {
            geneExpression = geneExpressionCache.data;
        }
    }
    
    // Sample data based on sample rate
    // For spheres, reduce max points slightly for performance
    let indicesToRender = [];
    const visibleCount = visibleIndices.length;
    
    // Calculate target count based on sample rate, but cap at MAX_POINTS for performance
    // When sample rate is 100%, show all points (up to MAX_POINTS limit for performance)
    const targetCount = Math.min(Math.floor(visibleCount * sampleRate), MAX_POINTS);
    
    if (targetCount >= visibleCount) {
        // If target is >= all points (100% sample rate and within limits), use all visible indices
        indicesToRender = Array.from(visibleIndices);
    } else {
        // Randomly sample targetCount points from visible indices
        // Convert Uint32Array to regular array for shuffling
        const allVisibleIndices = Array.from(visibleIndices);
        
        // Fisher-Yates shuffle algorithm for random sampling
        // We only need to shuffle the first targetCount elements
        for (let i = 0; i < targetCount && i < allVisibleIndices.length; i++) {
            // Pick a random index from remaining unshuffled portion
            const j = i + Math.floor(Math.random() * (allVisibleIndices.length - i));
            // Swap
            [allVisibleIndices[i], allVisibleIndices[j]] = [allVisibleIndices[j], allVisibleIndices[i]];
        }
        
        // Take the first targetCount elements (which are now randomly selected)
        indicesToRender = allVisibleIndices.slice(0, targetCount);
    }
    
    const count = indicesToRender.length;
    
    // Create sphere geometry for instancing
    const sphereGeometry = new THREE.SphereGeometry(pointSize, 8, 6); // radius, widthSegments, heightSegments
    
    // Create instanced mesh
    sphereMesh = new THREE.InstancedMesh(sphereGeometry, null, count);
    
    // Create material with instanced colors support
    const material = new THREE.MeshPhongMaterial({
        color: 0xffffff, // Base color (will be overridden by instance colors)
        transparent: true,
        opacity: 0.8,
        flatShading: true // Use flat shading for better performance
    });
    sphereMesh.material = material;
    
    // Enable instanced colors
    const colors = new Float32Array(count * 3);
    
    // Set up instance matrices and colors
    const matrix = new THREE.Matrix4();
    
    // Create geometry for bounding box calculation
    const positions = new Float32Array(count * 3);
    
    for (let i = 0; i < count; i++) {
        const dataIdx = indicesToRender[i];
        const point = allData[dataIdx];
        
        // Set position
        matrix.makeTranslation(point.x, point.y, point.z);
        sphereMesh.setMatrixAt(i, matrix);
        
        // Set color - handle gene expression specially
        let valueForColor;
        if (colorByGene && geneExpression) {
            valueForColor = geneExpression[dataIdx];
        } else {
            valueForColor = point[colorBy];
        }
        const pointColor = getColorForValue(valueForColor, effectiveColorBy);
        sphereMesh.setColorAt(i, pointColor);
        
        // Store position for bounding box
        positions[i * 3] = point.x;
        positions[i * 3 + 1] = point.y;
        positions[i * 3 + 2] = point.z;
    }
    
    // Update instance matrices and colors
    sphereMesh.instanceMatrix.needsUpdate = true;
    if (sphereMesh.instanceColor) {
        sphereMesh.instanceColor.needsUpdate = true;
    }
    
    scene.add(sphereMesh);
    pointCloud = sphereMesh; // Keep reference for cleanup
    
    // Store mapping from instance index to data index for hover detection
    renderedIndicesMap = indicesToRender;
    
    // Update legend
    updateLegend();
    
    // Update info
    const isSampled = indicesToRender.length < visibleIndices.length;
    document.getElementById('visibleCount').textContent = 
        `Visible points: ${indicesToRender.length.toLocaleString()}${isSampled ? ` (sampled from ${visibleIndices.length.toLocaleString()})` : ''}`;
    
    // Auto-adjust camera for x-y plane view only on first render
    if (!cameraInitialized) {
        const tempGeometry = new THREE.BufferGeometry();
        tempGeometry.setAttribute('position', new THREE.BufferAttribute(positions, 3));
        tempGeometry.computeBoundingBox();
        setCameraToXYPlaneView(tempGeometry);
        tempGeometry.dispose();
        cameraInitialized = true;
    }
}

// Create a filter UI element
function createFilterElement(filterId, attribute) {
    const filterDiv = document.createElement('div');
    filterDiv.className = 'filter-block';
    filterDiv.dataset.filterId = filterId;
    
    const availableAttributes = [...column_names_categorical, ...column_names_continuous];
    const availableOptions = availableAttributes.map(attr => 
        `<option value="${attr}" ${attr === attribute ? 'selected' : ''}>${attr}</option>`
    ).join('');
    
    if (column_names_continuous.includes(attribute)) {
        // Continuous filter with sliders
        const range = continuousRanges[attribute];
        if (!range || range.min === Infinity || range.max === -Infinity) {
            // Range not loaded yet, show placeholder
            filterDiv.innerHTML = `
            <div class="filter-header">
                <select class="filter-attribute" data-filter-id="${filterId}">
                    <option value="">Select attribute...</option>
                    ${availableOptions}
                </select>
                <button class="remove-filter" data-filter-id="${filterId}">×</button>
            </div>
            <div class="filter-content" data-filter-id="${filterId}">
                <p style="color: #95a5a6; font-size: 0.85em;">Loading range data...</p>
            </div>
            `;
            return filterDiv;
        }
        
        // Get the filter object to check if it has existing range values
        const filter = activeFilters.find(f => f.id === filterId);
        const currentMin = filter && filter.range ? filter.range.min : range.min;
        const currentMax = filter && filter.range ? filter.range.max : range.max;
        
        const rangeSize = range.max - range.min;
        const stepSize = rangeSize > 0 ? Math.max(rangeSize / 1000, 0.0001) : 0.0001;
        
        filterDiv.innerHTML = `
            <div class="filter-header">
                <select class="filter-attribute" data-filter-id="${filterId}">
                    <option value="">Select attribute...</option>
                    ${availableOptions}
                </select>
                <button class="remove-filter" data-filter-id="${filterId}">×</button>
            </div>
            <div class="filter-content" data-filter-id="${filterId}">
                <label>${attribute} Range:</label>
                <div class="time-slider-wrapper">
                    <input type="range" class="time-min" data-filter-id="${filterId}" 
                           min="${range.min}" max="${range.max}" 
                           step="${stepSize}" value="${currentMin}">
                    <input type="range" class="time-max" data-filter-id="${filterId}" 
                           min="${range.min}" max="${range.max}" 
                           step="${stepSize}" value="${currentMax}">
                </div>
                <div class="time-values">
                    <span>Min: <span class="time-min-value">${currentMin.toFixed(4)}</span></span>
                    <span>Max: <span class="time-max-value">${currentMax.toFixed(4)}</span></span>
                </div>
            </div>
        `;
    } else if (attribute) {
        // Categorical filter with checkboxes
        const values = Array.from(attributeValues[attribute] || []).sort();
        const filter = activeFilters.find(f => f.id === filterId);
        const selectedValues = filter && filter.values ? filter.values : new Set(values);
        
        const checkboxes = values.map(value => {
            const checked = selectedValues.has(value) ? 'checked' : '';
            return `
            <div class="filter-checkbox-item">
                <input type="checkbox" class="filter-checkbox" data-filter-id="${filterId}" 
                       value="${value}" ${checked}>
                <label>${value || '(empty)'}</label>
            </div>
        `;
        }).join('');
        
        filterDiv.innerHTML = `
            <div class="filter-header">
                <select class="filter-attribute" data-filter-id="${filterId}">
                    <option value="">Select attribute...</option>
                    ${availableOptions}
                </select>
                <button class="remove-filter" data-filter-id="${filterId}">×</button>
            </div>
            <div class="filter-content" data-filter-id="${filterId}">
                <div class="filter-checkboxes-container">
                    ${checkboxes}
                </div>
                <div class="filter-buttons">
                    <button class="select-all-filter" data-filter-id="${filterId}">Select All</button>
                    <button class="deselect-all-filter" data-filter-id="${filterId}">Deselect All</button>
                </div>
            </div>
        `;
    } else {
        // Empty filter
        filterDiv.innerHTML = `
            <div class="filter-header">
                <select class="filter-attribute" data-filter-id="${filterId}">
                    <option value="">Select attribute...</option>
                    ${availableOptions}
                </select>
                <button class="remove-filter" data-filter-id="${filterId}">×</button>
            </div>
            <div class="filter-content" data-filter-id="${filterId}">
                <p style="color: #95a5a6; font-size: 0.85em;">Select an attribute to filter by</p>
            </div>
        `;
    }
    
    return filterDiv;
}

// Render all active filters
function renderFilters() {
    const container = document.getElementById('filtersContainer');
    container.innerHTML = '';
    
    if (activeFilters.length === 0) {
        return;
    }
    
    activeFilters.forEach((filter, index) => {
        const filterElement = createFilterElement(filter.id, filter.attribute);
        container.appendChild(filterElement);
    });
    
    // Attach event listeners
    attachFilterEventListeners();
}

// Attach event listeners to filter elements
function attachFilterEventListeners() {
    // Attribute change
    document.querySelectorAll('.filter-attribute').forEach(select => {
        // Remove existing listeners by cloning
        const newSelect = select.cloneNode(true);
        select.parentNode.replaceChild(newSelect, select);
        
        newSelect.addEventListener('change', async (e) => {
            const filterId = e.target.dataset.filterId;
            const attribute = e.target.value;
            
            const filter = activeFilters.find(f => f.id === filterId);
            if (filter && attribute) {
                filter.attribute = attribute;
                
                // Ensure the column is loaded
                await ensureColumnLoaded(attribute);
                
                if (column_names_continuous.includes(attribute)) {
                    filter.type = 'continuous';
                    const range = continuousRanges[attribute];
                    filter.range = range ? { min: range.min, max: range.max } : { min: 0, max: 1 };
                    filter.values = null;
                } else if (column_names_categorical.includes(attribute)) {
                    filter.type = 'categorical';
                    const values = Array.from(attributeValues[attribute] || []);
                    filter.values = new Set(values);
                    filter.range = null;
                } else {
                    filter.type = null;
                    filter.values = null;
                    filter.range = null;
                }
                renderFilters();
                throttleFilterUpdate();
            }
        });
    });
    
    // Remove filter
    document.querySelectorAll('.remove-filter').forEach(btn => {
        btn.addEventListener('click', (e) => {
            const filterId = e.target.dataset.filterId;
            const filterToRemove = activeFilters.find(f => f.id === filterId);
            if (filterToRemove) {
                console.log('[Filter] Removing filter:', {
                    id: filterId,
                    attribute: filterToRemove.attribute,
                    type: filterToRemove.type
                });
            }
            activeFilters = activeFilters.filter(f => f.id !== filterId);
            console.log('[Filter] Active filters after removal:', activeFilters.length);
            renderFilters();
            throttleFilterUpdate();
        });
    });
    
    // Time sliders - need to attach fresh each time
    document.querySelectorAll('.time-min').forEach(slider => {
        // Clone to remove old listeners
        const newSlider = slider.cloneNode(true);
        slider.parentNode.replaceChild(newSlider, slider);
        
        newSlider.addEventListener('input', (e) => {
            const filterId = e.target.dataset.filterId;
            const minVal = parseFloat(e.target.value);
            const filter = activeFilters.find(f => f.id === filterId);
            
            if (filter && filter.range) {
                if (minVal > filter.range.max) {
                    filter.range.max = minVal;
                    const maxSlider = document.querySelector(`.time-max[data-filter-id="${filterId}"]`);
                    if (maxSlider) maxSlider.value = minVal;
                    const maxValueEl = document.querySelector(`.time-max-value[data-filter-id="${filterId}"]`);
                    if (maxValueEl) maxValueEl.textContent = minVal.toFixed(4);
                }
                filter.range.min = minVal;
                const minValueEl = document.querySelector(`.time-min-value[data-filter-id="${filterId}"]`);
                if (minValueEl) minValueEl.textContent = minVal.toFixed(4);
                throttleFilterUpdate();
            }
        });
    });
    
    document.querySelectorAll('.time-max').forEach(slider => {
        // Clone to remove old listeners
        const newSlider = slider.cloneNode(true);
        slider.parentNode.replaceChild(newSlider, slider);
        
        newSlider.addEventListener('input', (e) => {
            const filterId = e.target.dataset.filterId;
            const maxVal = parseFloat(e.target.value);
            const filter = activeFilters.find(f => f.id === filterId);
            
            if (filter && filter.range) {
                if (maxVal < filter.range.min) {
                    filter.range.min = maxVal;
                    const minSlider = document.querySelector(`.time-min[data-filter-id="${filterId}"]`);
                    if (minSlider) minSlider.value = maxVal;
                    const minValueEl = document.querySelector(`.time-min-value[data-filter-id="${filterId}"]`);
                    if (minValueEl) minValueEl.textContent = maxVal.toFixed(4);
                }
                filter.range.max = maxVal;
                const maxValueEl = document.querySelector(`.time-max-value[data-filter-id="${filterId}"]`);
                if (maxValueEl) maxValueEl.textContent = maxVal.toFixed(4);
                throttleFilterUpdate();
            }
        });
    });
    
    // Categorical checkboxes
    document.querySelectorAll('.filter-checkbox').forEach(checkbox => {
        checkbox.addEventListener('change', () => {
            const filterId = checkbox.dataset.filterId;
            const filter = activeFilters.find(f => f.id === filterId);
            
            if (filter && filter.values) {
                const allCheckboxes = document.querySelectorAll(`.filter-checkbox[data-filter-id="${filterId}"]`);
                filter.values.clear();
                allCheckboxes.forEach(cb => {
                    if (cb.checked) {
                        filter.values.add(cb.value);
                    }
                });
                throttleFilterUpdate();
            }
        });
    });
    
    // Select all / Deselect all buttons
    document.querySelectorAll('.select-all-filter').forEach(btn => {
        btn.addEventListener('click', (e) => {
            const filterId = e.target.dataset.filterId;
            document.querySelectorAll(`.filter-checkbox[data-filter-id="${filterId}"]`).forEach(cb => {
                cb.checked = true;
            });
            const filter = activeFilters.find(f => f.id === filterId);
            if (filter && filter.values) {
                const allCheckboxes = document.querySelectorAll(`.filter-checkbox[data-filter-id="${filterId}"]`);
                filter.values.clear();
                allCheckboxes.forEach(cb => filter.values.add(cb.value));
                throttleFilterUpdate();
            }
        });
    });
    
    document.querySelectorAll('.deselect-all-filter').forEach(btn => {
        btn.addEventListener('click', (e) => {
            const filterId = e.target.dataset.filterId;
            document.querySelectorAll(`.filter-checkbox[data-filter-id="${filterId}"]`).forEach(cb => {
                cb.checked = false;
            });
            const filter = activeFilters.find(f => f.id === filterId);
            if (filter && filter.values) {
                filter.values.clear();
                throttleFilterUpdate();
            }
        });
    });
}

// Throttle function for filter updates
let filterUpdateTimeout = null;
function throttleFilterUpdate() {
    if (filterUpdateTimeout) {
        clearTimeout(filterUpdateTimeout);
    }
    filterUpdateTimeout = setTimeout(async () => {
        await updateFilter();
    }, 100); // 100ms throttle
}

// Update filter - optimized for performance, applies all active filters
async function updateFilter() {
    console.log('[Filter] Updating filters, active filters:', activeFilters.length);
    
    // If no active filters, show all points
    if (activeFilters.length === 0) {
        visibleIndices = new Uint32Array(allData.length);
        for (let i = 0; i < allData.length; i++) {
            visibleIndices[i] = i;
        }
        console.log(`[Filter] No filters active - showing all ${visibleIndices.length} points`);
        await createPointCloud();
        return;
    }
    
    // Start with all indices
    let candidateIndices = [];
    for (let i = 0; i < allData.length; i++) {
        candidateIndices.push(i);
    }
    
    // Ensure all filter columns are loaded
    const filterColumns = activeFilters
        .filter(f => f.attribute && f.type)
        .map(f => f.attribute);
    await ensureColumnsLoaded(filterColumns);
    
    // Apply each filter sequentially (AND logic)
    for (const filter of activeFilters) {
        if (!filter.attribute || !filter.type) {
            console.log(`[Filter] Skipping filter (no attribute or type)`);
            continue;
        }
        
        const filteredIndices = [];
        const beforeCount = candidateIndices.length;
        
        if (filter.type === 'continuous' && filter.range) {
            // Continuous range filter
            const minVal = filter.range.min;
            const maxVal = filter.range.max;
            
            for (let idx of candidateIndices) {
                const point = allData[idx];
                const value = point[filter.attribute];
                if (value !== null && value !== undefined && value >= minVal && value <= maxVal) {
                    filteredIndices.push(idx);
                }
            }
            console.log(`[Filter] Applied continuous filter on ${filter.attribute}: ${beforeCount} -> ${filteredIndices.length} points`);
        } else if (filter.type === 'categorical' && filter.values && filter.values.size > 0) {
            // Categorical filter
            for (let idx of candidateIndices) {
                const point = allData[idx];
                if (filter.values.has(point[filter.attribute] || '')) {
                    filteredIndices.push(idx);
                }
            }
            console.log(`[Filter] Applied categorical filter on ${filter.attribute}: ${beforeCount} -> ${filteredIndices.length} points`);
        } else {
            // Invalid filter, skip it (don't filter anything)
            console.log(`[Filter] Skipping invalid filter on ${filter.attribute}`);
            continue;
        }
        
        candidateIndices = filteredIndices;
    }
    
    // Convert to Uint32Array
    visibleIndices = new Uint32Array(candidateIndices);
    
    console.log(`[Filter] Final visible points: ${visibleIndices.length} out of ${allData.length} total`);
    
    await createPointCloud();
    // Legend updates automatically when point cloud is recreated
}

// Setup tab switching
function setupTabs() {
    const tabButtons = document.querySelectorAll('.tab-btn');
    const tabContents = document.querySelectorAll('.tab-content');
    
    tabButtons.forEach(btn => {
        btn.addEventListener('click', async () => {
            const tabId = btn.dataset.tab;
            
            // Update button states
            tabButtons.forEach(b => b.classList.remove('active'));
            btn.classList.add('active');
            
            // Update content visibility
            tabContents.forEach(content => {
                content.classList.remove('active');
                if (content.id === `${tabId}-tab`) {
                    content.classList.add('active');
                }
            });
            
            // Initialize gene table when first switching to genes tab
            if (tabId === 'genes' && !geneTable && sparseMatrix.geneNames && sparseMatrix.geneNames.length > 0) {
                // Load var columns if not already loaded
                if (!varColumnsLoaded) {
                    const loadingEl = document.getElementById('loading');
                    const loadingText = loadingEl.querySelector('.loading-text');
                    loadingEl.style.display = 'flex';
                    loadingText.textContent = 'Loading gene statistics...';
                    await ensureVarColumnsLoaded();
                    loadingEl.style.display = 'none';
                }
                initGeneTable();
            }
        });
    });
}

// Initialize the gene statistics table
function initGeneTable() {
    if (geneTable) return;
    
    // Determine which columns to show and their order
    // Priority order for important columns (using normalized names - dots replaced with underscores)
    const priorityColumns = [
        'gene',           // Always first
        'highly_variable',
        'dispersions_norm',
        'dispersions',
        'means',
        'mt',
        'highly_variable_intersection',
        'highly_variable_nbatches'
    ];
    
    // Get all available columns from the first gene stat entry
    // Note: these are already normalized (dots replaced with underscores)
    const allColumns = geneStats.length > 0 ? Object.keys(geneStats[0]) : [];
    
    // Build column order: priority columns first, then rest
    const columnOrder = [];
    const usedColumns = new Set();
    
    // Add priority columns that exist (check normalized names)
    for (const col of priorityColumns) {
        if (allColumns.includes(col)) {
            columnOrder.push(col);
            usedColumns.add(col);
        }
    }
    
    // Add remaining columns (excluding 'gene' which is already added)
    for (const col of allColumns) {
        if (!usedColumns.has(col) && col !== 'gene') {
            columnOrder.push(col);
        }
    }
    
    // Build Tabulator column definitions
    // Note: columnOrder contains normalized field names (dots replaced with underscores)
    const tableColumns = columnOrder.map(fieldName => {
        // Get original column name for display (if mapping exists)
        const originalName = window.varFieldNameMapping && window.varFieldNameMapping[fieldName] 
            ? window.varFieldNameMapping[fieldName] 
            : fieldName;
        
        // Check if it's a boolean/categorical column
        const sampleValue = geneStats.length > 0 ? geneStats[0][fieldName] : null;
        const isBoolean = typeof sampleValue === 'boolean';
        const isNumeric = typeof sampleValue === 'number' && !isNaN(sampleValue);
        
        // Calculate minimum width based on header text length
        const headerText = originalName.replace(/_/g, ' ').replace(/\b\w/g, l => l.toUpperCase());
        // Minimum width: at least 120px, or 8px per character in header text, whichever is larger
        const minWidth = Math.max(120, headerText.length * 8);
        
        const colDef = {
            title: headerText,
            field: fieldName,  // Use normalized field name (without dots)
            sorter: isNumeric ? 'number' : 'string',
            headerFilter: 'input',
            headerFilterPlaceholder: 'Filter...',
            minWidth: minWidth,
            width: minWidth  // Set initial width to minimum
        };
        
        if (isBoolean) {
            // Boolean column - show as Yes/No
            colDef.formatter = (cell) => {
                const val = cell.getValue();
                return val === true ? 'Yes' : val === false ? 'No' : '-';
            };
            colDef.sorter = 'boolean';
        } else if (isNumeric) {
            // Numeric column - format with appropriate precision
            colDef.formatter = (cell) => {
                const val = cell.getValue();
                if (val === null || val === undefined) return '-';
                // Use more precision for small numbers, less for large
                if (Math.abs(val) < 0.01 || Math.abs(val) > 1000) {
                    return val.toExponential(3);
                } else {
                    return val.toFixed(4);
                }
            };
        } else {
            // String/categorical column
            colDef.formatter = (cell) => {
                const val = cell.getValue();
                return val !== null && val !== undefined ? String(val) : '-';
            };
        }
        
        return colDef;
    });
    
    // Make gene column frozen
    const geneColIndex = tableColumns.findIndex(col => col.field === 'gene');
    if (geneColIndex >= 0) {
        tableColumns[geneColIndex].frozen = true;
        tableColumns[geneColIndex].width = 150;
    }
    
    // Determine initial sort column (prefer dispersions_norm, then highly_variable, then means)
    let initialSortColumn = 'gene';
    if (columnOrder.includes('dispersions_norm')) {
        initialSortColumn = 'dispersions_norm';
    } else if (columnOrder.includes('highly_variable')) {
        initialSortColumn = 'highly_variable';
    } else if (columnOrder.includes('means')) {
        initialSortColumn = 'means';
    }
    
    geneTable = new Tabulator('#gene-table', {
        data: geneStats,
        layout: 'fitDataStretch',  // Use fitDataStretch to allow columns to grow but respect minWidth
        height: '100%',
        placeholder: 'No gene data available',
        initialSort: [{ column: initialSortColumn, dir: 'desc' }],
        columns: tableColumns,
    });
    
    // Use event listener syntax for row click (more reliable in Tabulator 6)
    geneTable.on('rowClick', (e, row) => {
        const gene = row.getData().gene;
        console.log('[GeneTable] Row clicked, gene:', gene);
        if (selectGeneGlobal) {
            selectGeneGlobal(gene);
        }
    });
    
    console.log('[initGeneTable] Gene table initialized with', geneStats.length, 'genes and', tableColumns.length, 'columns');
}

// Add gene winsorization controls to legend (styled like continuous filter)
function addGeneWinsorizationControlsToLegend(legendDiv, colorBy) {
    // Remove any existing winsorization controls
    const existingControls = legendDiv.querySelector('.gene-winsorization-controls');
    if (existingControls) {
        existingControls.remove();
    }
    
    // Check if Color By is set to "Gene" and a gene is selected
    const colorBySelect = document.getElementById('colorBy');
    const colorByValue = colorBySelect ? colorBySelect.value : '';
    const isColoringByGene = colorByValue === 'Gene' && selectedGene !== null && geneExpressionCache.geneName === selectedGene;
    
    if (!isColoringByGene) return;
    
    const actualMin = geneExpressionCache.min;
    const actualMax = geneExpressionCache.max;
    const currentWinMin = geneExpressionCache.winsorizedMin !== undefined ? geneExpressionCache.winsorizedMin : actualMin;
    const currentWinMax = geneExpressionCache.winsorizedMax !== undefined ? geneExpressionCache.winsorizedMax : actualMax;
    
    // Calculate step size based on range
    const rangeSize = actualMax - actualMin;
    const stepSize = rangeSize > 0 ? Math.max(rangeSize / 1000, 0.0001) : 0.0001;
    
    // Create controls container (styled like filter)
    const controlsDiv = document.createElement('div');
    controlsDiv.className = 'gene-winsorization-controls';
    controlsDiv.style.marginTop = '16px';
    controlsDiv.style.paddingTop = '16px';
    controlsDiv.style.borderTop = '1px solid rgba(255, 255, 255, 0.15)';
    
    // Add label (like filter)
    const label = document.createElement('label');
    label.textContent = `${selectedGene} Range:`;
    label.style.display = 'block';
    label.style.marginBottom = '8px';
    label.style.fontSize = '0.9em';
    label.style.color = 'rgba(255, 255, 255, 0.7)';
    controlsDiv.appendChild(label);
    
    // Add slider wrapper (same as filter)
    const sliderWrapper = document.createElement('div');
    sliderWrapper.className = 'time-slider-wrapper';
    
    const minSlider = document.createElement('input');
    minSlider.type = 'range';
    minSlider.className = 'time-min';
    minSlider.id = 'geneMinSlider';
    minSlider.min = actualMin;
    minSlider.max = actualMax;
    minSlider.step = stepSize;
    minSlider.value = currentWinMin;
    
    const maxSlider = document.createElement('input');
    maxSlider.type = 'range';
    maxSlider.className = 'time-max';
    maxSlider.id = 'geneMaxSlider';
    maxSlider.min = actualMin;
    maxSlider.max = actualMax;
    maxSlider.step = stepSize;
    maxSlider.value = currentWinMax;
    
    sliderWrapper.appendChild(minSlider);
    sliderWrapper.appendChild(maxSlider);
    controlsDiv.appendChild(sliderWrapper);
    
    // Add values display (same as filter)
    const valuesDiv = document.createElement('div');
    valuesDiv.className = 'time-values';
    
    const minSpan = document.createElement('span');
    minSpan.innerHTML = `Min: <span id="geneMinValue">${currentWinMin.toFixed(4)}</span>`;
    
    const maxSpan = document.createElement('span');
    maxSpan.innerHTML = `Max: <span id="geneMaxValue">${currentWinMax.toFixed(4)}</span>`;
    
    valuesDiv.appendChild(minSpan);
    valuesDiv.appendChild(maxSpan);
    controlsDiv.appendChild(valuesDiv);
    
    // Add reset button
    const resetBtn = document.createElement('button');
    resetBtn.id = 'resetGeneRange';
    resetBtn.textContent = 'Reset to Full Range';
    resetBtn.className = 'reset-gene-range-btn';
    resetBtn.style.marginTop = '8px';
    controlsDiv.appendChild(resetBtn);
    
    legendDiv.appendChild(controlsDiv);
    
    // Attach event listeners
    attachGeneWinsorizationListeners();
}

// Attach event listeners for gene winsorization controls
function attachGeneWinsorizationListeners() {
    // Remove old listeners by cloning elements
    const geneMinSlider = document.getElementById('geneMinSlider');
    const geneMaxSlider = document.getElementById('geneMaxSlider');
    const resetGeneRangeBtn = document.getElementById('resetGeneRange');
    
    if (geneMinSlider) {
        // Clone to remove old listeners
        const newSlider = geneMinSlider.cloneNode(true);
        geneMinSlider.parentNode.replaceChild(newSlider, geneMinSlider);
        
        // Use throttling for slider input to avoid too many updates
        let minSliderTimeout = null;
        newSlider.addEventListener('input', (e) => {
            // Update display value in real-time
            const geneMinValue = document.getElementById('geneMinValue');
            if (geneMinValue) {
                geneMinValue.textContent = parseFloat(e.target.value).toFixed(4);
            }
            
            // Throttle the actual update
            if (minSliderTimeout) {
                clearTimeout(minSliderTimeout);
            }
            minSliderTimeout = setTimeout(async () => {
                await handleGeneMinWinsorizationChange();
            }, 100);
        });
    }
    
    if (geneMaxSlider) {
        // Clone to remove old listeners
        const newSlider = geneMaxSlider.cloneNode(true);
        geneMaxSlider.parentNode.replaceChild(newSlider, geneMaxSlider);
        
        // Use throttling for slider input to avoid too many updates
        let maxSliderTimeout = null;
        newSlider.addEventListener('input', (e) => {
            // Update display value in real-time
            const geneMaxValue = document.getElementById('geneMaxValue');
            if (geneMaxValue) {
                geneMaxValue.textContent = parseFloat(e.target.value).toFixed(4);
            }
            
            // Throttle the actual update
            if (maxSliderTimeout) {
                clearTimeout(maxSliderTimeout);
            }
            maxSliderTimeout = setTimeout(async () => {
                await handleGeneMaxWinsorizationChange();
            }, 100);
        });
    }
    
    if (resetGeneRangeBtn) {
        // Clone to remove old listeners
        const newBtn = resetGeneRangeBtn.cloneNode(true);
        resetGeneRangeBtn.parentNode.replaceChild(newBtn, resetGeneRangeBtn);
        newBtn.addEventListener('click', resetGeneWinsorization);
    }
}

// Update gene winsorization controls (now called when legend updates)
function updateGeneWinsorizationControls() {
    // Controls are now added dynamically to legend, so this function is called from updateLegend
    // We just need to make sure the legend is updated
    updateLegend();
}

// Handle gene winsorization change (for min slider)
async function handleGeneMinWinsorizationChange() {
    const geneMinSlider = document.getElementById('geneMinSlider');
    const geneMaxSlider = document.getElementById('geneMaxSlider');
    const geneMinValue = document.getElementById('geneMinValue');
    
    if (!geneMinSlider || !geneMaxSlider || !selectedGene) return;
    
    const newMin = parseFloat(geneMinSlider.value);
    const currentMax = parseFloat(geneMaxSlider.value);
    
    if (isNaN(newMin)) return;
    
    // Ensure min < max - if min exceeds max, adjust max
    if (newMin >= currentMax) {
        const newMax = newMin + 0.0001; // Add small increment
        if (newMax <= geneExpressionCache.max) {
            geneMaxSlider.value = newMax;
            geneExpressionCache.winsorizedMax = newMax;
            geneMaxValue.textContent = newMax.toFixed(4);
        } else {
            // Can't increase max, so reset min
            geneMinSlider.value = currentMax - 0.0001;
            return;
        }
    }
    
    // Update winsorized range
    geneExpressionCache.winsorizedMin = newMin;
    geneMinValue.textContent = newMin.toFixed(4);
    
    console.log(`[handleGeneMinWinsorizationChange] Updated winsorization min: ${newMin.toFixed(4)}`);
    
    // Recreate point cloud with new color scale
    await createPointCloud();
    updateLegend();
}

// Handle gene winsorization change (for max slider)
async function handleGeneMaxWinsorizationChange() {
    const geneMinSlider = document.getElementById('geneMinSlider');
    const geneMaxSlider = document.getElementById('geneMaxSlider');
    const geneMaxValue = document.getElementById('geneMaxValue');
    
    if (!geneMinSlider || !geneMaxSlider || !selectedGene) return;
    
    const newMax = parseFloat(geneMaxSlider.value);
    const currentMin = parseFloat(geneMinSlider.value);
    
    if (isNaN(newMax)) return;
    
    // Ensure min < max - if max is below min, adjust min
    if (newMax <= currentMin) {
        const newMin = newMax - 0.0001; // Subtract small increment
        if (newMin >= geneExpressionCache.min) {
            geneMinSlider.value = newMin;
            geneExpressionCache.winsorizedMin = newMin;
            geneMinValue.textContent = newMin.toFixed(4);
        } else {
            // Can't decrease min, so reset max
            geneMaxSlider.value = currentMin + 0.0001;
            return;
        }
    }
    
    // Update winsorized range
    geneExpressionCache.winsorizedMax = newMax;
    geneMaxValue.textContent = newMax.toFixed(4);
    
    console.log(`[handleGeneMaxWinsorizationChange] Updated winsorization max: ${newMax.toFixed(4)}`);
    
    // Recreate point cloud with new color scale
    await createPointCloud();
    updateLegend();
}

// Reset gene winsorization to full range
async function resetGeneWinsorization() {
    if (!selectedGene || !geneExpressionCache.geneName) return;
    
    geneExpressionCache.winsorizedMin = geneExpressionCache.min;
    geneExpressionCache.winsorizedMax = geneExpressionCache.max;
    
    // Update legend (which will recreate the controls with new values)
    updateLegend();
    await createPointCloud();
}

// Update coordinate selection UI
function updateCoordinateSelectionUI() {
    const xSelect = document.getElementById('coordX');
    const ySelect = document.getElementById('coordY');
    const zSelect = document.getElementById('coordZ');
    
    if (!xSelect || !ySelect || !zSelect) return;
    
    // Clear existing options
    xSelect.innerHTML = '';
    ySelect.innerHTML = '';
    zSelect.innerHTML = '';
    
    // Add "None" option to Z coordinate
    const noneOption = document.createElement('option');
    noneOption.value = 'none';
    noneOption.textContent = 'None';
    if (!selectedZCoord) {
        noneOption.selected = true;
    }
    zSelect.appendChild(noneOption);
    
    // Only add obsm options (obs columns are not used for coordinates)
    // Add obsm options
    availableCoordinateSources.obsm.forEach(coord => {
        const optionX = document.createElement('option');
        // Use columnName if available, otherwise use columnIndex
        const value = coord.columnName ? 
            `obsm:${coord.embedding}:${coord.columnName}` : 
            `obsm:${coord.embedding}:${coord.columnIndex}`;
        optionX.value = value;
        optionX.textContent = coord.displayName;
        if (selectedXCoord && selectedXCoord.source === 'obsm' && 
            selectedXCoord.embedding === coord.embedding && 
            selectedXCoord.columnIndex === coord.columnIndex) {
            optionX.selected = true;
        }
        xSelect.appendChild(optionX);
        
        const optionY = document.createElement('option');
        optionY.value = value;
        optionY.textContent = coord.displayName;
        if (selectedYCoord && selectedYCoord.source === 'obsm' && 
            selectedYCoord.embedding === coord.embedding && 
            selectedYCoord.columnIndex === coord.columnIndex) {
            optionY.selected = true;
        }
        ySelect.appendChild(optionY);
        
        // Add to Z coordinate dropdown as well
        const optionZ = document.createElement('option');
        optionZ.value = value;
        optionZ.textContent = coord.displayName;
        if (selectedZCoord && selectedZCoord.source === 'obsm' && 
            selectedZCoord.embedding === coord.embedding && 
            selectedZCoord.columnIndex === coord.columnIndex) {
            optionZ.selected = true;
        }
        zSelect.appendChild(optionZ);
    });
}

// Handle coordinate selection change
async function handleCoordinateChange() {
    const xSelect = document.getElementById('coordX');
    const ySelect = document.getElementById('coordY');
    const zSelect = document.getElementById('coordZ');
    
    if (!xSelect || !ySelect || !zSelect || !zarrRoot) return;
    
    const xValue = xSelect.value;
    const yValue = ySelect.value;
    const zValue = zSelect.value;
    
    // Parse coordinate source (only obsm sources are allowed)
    function parseCoordSource(value) {
        if (!value || value === 'none') return null;
        const parts = value.split(':');
        if (parts.length < 2) return null;
        
        // Only parse obsm sources (obs sources are not used for coordinates)
        if (parts[0] === 'obsm' && parts.length >= 3) {
            const embedding = parts[1];
            // For obsm, the value format is "obsm:embedding:columnIndex" or "obsm:embedding:columnName"
            // Try to parse as integer first (column index)
            const colIdx = parseInt(parts[2]);
            if (!isNaN(colIdx)) {
                return availableCoordinateSources.obsm.find(c => 
                    c.embedding === embedding && c.columnIndex === colIdx);
            } else {
                // Try to match by column name
                const match = availableCoordinateSources.obsm.find(c => 
                    c.embedding === embedding && c.columnName === parts[2]);
                if (match) return match;
                // If no match by name, try to find by embedding and use first column
                return availableCoordinateSources.obsm.find(c => c.embedding === embedding);
            }
        }
        return null;
    }
    
    const newXCoord = parseCoordSource(xValue);
    const newYCoord = parseCoordSource(yValue);
    const newZCoord = parseCoordSource(zValue); // Can be null for "None"
    
    if (!newXCoord || !newYCoord) {
        console.warn('[handleCoordinateChange] Invalid coordinate selection');
        return;
    }
    
    selectedXCoord = newXCoord;
    selectedYCoord = newYCoord;
    selectedZCoord = newZCoord; // Can be null
    
    console.log('[handleCoordinateChange] Loading new coordinates:', {
        x: selectedXCoord.displayName,
        y: selectedYCoord.displayName,
        z: selectedZCoord ? selectedZCoord.displayName : 'None'
    });
    
    // Load new coordinate values
    const nCells = allData.length;
    const xValues = await loadCoordinateValues(zarrRoot, selectedXCoord, nCells);
    const yValues = await loadCoordinateValues(zarrRoot, selectedYCoord, nCells);
    const zValues = selectedZCoord ? await loadCoordinateValues(zarrRoot, selectedZCoord, nCells) : null;
    
    // Update data
    for (let i = 0; i < nCells; i++) {
        allData[i].x = xValues[i] || 0;
        allData[i].y = yValues[i] || 0;
        allData[i].z = zValues ? (zValues[i] || 0) : 0;
    }
    
    // Recreate point cloud with new coordinates
    await createPointCloud();
}

// Setup event listeners
function setupEventListeners() {
    // Setup tab switching
    setupTabs();
    
    document.getElementById('colorBy').addEventListener('change', async (e) => {
        const colorByValue = e.target.value;
        
        // If Color By is changed to "Gene" but no gene is selected, revert to first obs attribute
        if (colorByValue === 'Gene' && !selectedGene) {
            const obsAttributes = [...column_names_categorical, ...column_names_continuous];
            if (obsAttributes.length > 0) {
                e.target.value = obsAttributes[0];
                console.log('[ColorBy] Gene selected but no gene entered, reverting to first obs attribute');
            }
        }
        
        // Legend will be updated which handles winsorization controls visibility
        
        // Update colors immediately for color changes (no throttle needed, just recolor)
        if (pointCloud) {
            await createPointCloud();
        } else {
            // If no point cloud yet, just update legend
            updateLegend();
        }
    });
    
    // Add filter button
    document.getElementById('addFilter').addEventListener('click', () => {
        const filterId = 'filter_' + Date.now() + '_' + Math.random().toString(36).substr(2, 9);
        const newFilter = {
            id: filterId,
            attribute: '',
            type: null,
            values: null,
            range: null
        };
        activeFilters.push(newFilter);
        console.log('[Filter] Created new filter:', {
            id: filterId,
            totalFilters: activeFilters.length
        });
        renderFilters();
    });
    
    document.getElementById('pointSize').addEventListener('input', (e) => {
        document.getElementById('pointSizeValue').textContent = parseFloat(e.target.value).toFixed(1);
        // Recreate point cloud with new size
        if (visibleIndices && visibleIndices.length > 0) {
            throttleFilterUpdate();
        }
    });
    
    document.getElementById('sampleRate').addEventListener('input', (e) => {
        document.getElementById('sampleRateValue').textContent = e.target.value + '%';
        throttleFilterUpdate();
    });
    
    // Coordinate selection handlers
    const coordXSelect = document.getElementById('coordX');
    const coordYSelect = document.getElementById('coordY');
    const coordZSelect = document.getElementById('coordZ');
    if (coordXSelect) {
        coordXSelect.addEventListener('change', handleCoordinateChange);
    }
    if (coordYSelect) {
        coordYSelect.addEventListener('change', handleCoordinateChange);
    }
    if (coordZSelect) {
        coordZSelect.addEventListener('change', handleCoordinateChange);
    }
    
    // Gene winsorization handlers are now attached dynamically in addGeneWinsorizationControlsToLegend
    // No need to set them up here since controls are created dynamically
    
    document.getElementById('resetCamera').addEventListener('click', () => {
        if (pointCloud) {
            // Recalculate bounding box from current visible data
            const positions = [];
            if (visibleIndices && visibleIndices.length > 0) {
                const MAX_SAMPLE = 10000; // Sample points for bounding box calculation
                const step = Math.max(1, Math.floor(visibleIndices.length / MAX_SAMPLE));
                for (let i = 0; i < visibleIndices.length; i += step) {
                    const point = allData[visibleIndices[i]];
                    positions.push(point.x, point.y, point.z);
                }
            }
            
            if (positions.length > 0) {
                const tempGeometry = new THREE.BufferGeometry();
                tempGeometry.setAttribute('position', new THREE.BufferAttribute(new Float32Array(positions), 3));
                tempGeometry.computeBoundingBox();
                setCameraToXYPlaneView(tempGeometry);
                tempGeometry.dispose();
            } else if (initialCameraState.position && initialCameraState.target) {
                // Fall back to stored initial state
                camera.position.copy(initialCameraState.position);
                controls.target.copy(initialCameraState.target);
                camera.lookAt(initialCameraState.target);
                controls.update();
            }
        } else if (initialCameraState.position && initialCameraState.target) {
            // Use stored initial state if no point cloud yet
            camera.position.copy(initialCameraState.position);
            controls.target.copy(initialCameraState.target);
            camera.lookAt(initialCameraState.target);
            controls.update();
        }
    });
}

// Animation loop
function animate() {
    requestAnimationFrame(animate);
    controls.update();
    renderer.render(scene, camera);
}

// Initialize when page loads
window.addEventListener('DOMContentLoaded', () => {
    initScene();
    loadData();
});
